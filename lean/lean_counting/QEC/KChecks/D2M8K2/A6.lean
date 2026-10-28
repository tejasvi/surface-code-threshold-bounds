import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A5

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows7196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7196 = true := by
  rw [show D2M8K2.u7196 = KTree.node D2M8K2.t7200 (nat_lit 15164978) (nat_lit 3387738137) (nat_lit 0) D2M8K2.t7201 from rfl, allE_node, rows7200, irow7196, rows7201]
  all_goals rfl

theorem atot7196 : totK PD2M8K2 D2M8K2.u7196 = [0, 0, 379476686365, 944681605174, 478842624370, 32274309753, 0, 0] := by
  rw [show D2M8K2.u7196 = KTree.node D2M8K2.t7200 (nat_lit 15164978) (nat_lit 3387738137) (nat_lit 0) D2M8K2.t7201 from rfl, totK_node, tot7200, tot7201]
  decide +kernel

theorem arows7197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7197 = true := by
  rw [show D2M8K2.u7197 = KTree.node D2M8K2.t7202 (nat_lit 15166520) (nat_lit 2440270768) (nat_lit 0) D2M8K2.t7203 from rfl, allE_node, rows7202, irow7197, rows7203]
  all_goals rfl

theorem atot7197 : totK PD2M8K2 D2M8K2.u7197 = [0, 0, 192135926335, 783594441133, 701660096263, 95147293868, 1075657031, 0] := by
  rw [show D2M8K2.u7197 = KTree.node D2M8K2.t7202 (nat_lit 15166520) (nat_lit 2440270768) (nat_lit 0) D2M8K2.t7203 from rfl, totK_node, tot7202, tot7203]
  decide +kernel

theorem arows7199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7199 = true := by
  rw [show D2M8K2.u7199 = KTree.node D2M8K2.t7204 (nat_lit 15168550) (nat_lit 2861108828) (nat_lit 0) D2M8K2.t7205 from rfl, allE_node, rows7204, irow7199, rows7205]
  all_goals rfl

theorem atot7199 : totK PD2M8K2 D2M8K2.u7199 = [0, 0, 254005317067, 793743835062, 616668027396, 105943278002, 3804183361, 0] := by
  rw [show D2M8K2.u7199 = KTree.node D2M8K2.t7204 (nat_lit 15168550) (nat_lit 2861108828) (nat_lit 0) D2M8K2.t7205 from rfl, totK_node, tot7204, tot7205]
  decide +kernel

theorem arows7200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7200 = true := by
  rw [show D2M8K2.u7200 = KTree.node D2M8K2.t7206 (nat_lit 15175444) (nat_lit 3638873261) (nat_lit 0) D2M8K2.t7207 from rfl, allE_node, rows7206, irow7200, rows7207]
  all_goals rfl

theorem atot7200 : totK PD2M8K2 D2M8K2.u7200 = [0, 0, 382764183675, 953927814547, 447425609643, 27077175137, 0, 0] := by
  rw [show D2M8K2.u7200 = KTree.node D2M8K2.t7206 (nat_lit 15175444) (nat_lit 3638873261) (nat_lit 0) D2M8K2.t7207 from rfl, totK_node, tot7206, tot7207]
  decide +kernel

theorem arows7203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7203 = true := by
  rw [show D2M8K2.u7203 = KTree.node D2M8K2.t7208 (nat_lit 15176942) (nat_lit 2603329618) (nat_lit 0) D2M8K2.t7209 from rfl, allE_node, rows7208, irow7203, rows7209]
  all_goals rfl

theorem atot7203 : totK PD2M8K2 D2M8K2.u7203 = [0, 0, 179163009487, 767647214723, 732334482227, 115434568784, 1242138600, 0] := by
  rw [show D2M8K2.u7203 = KTree.node D2M8K2.t7208 (nat_lit 15176942) (nat_lit 2603329618) (nat_lit 0) D2M8K2.t7209 from rfl, totK_node, tot7208, tot7209]
  decide +kernel

theorem arows7204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7204 = true := by
  rw [show D2M8K2.u7204 = KTree.node D2M8K2.t7210 (nat_lit 15178837) (nat_lit 1269065816) (nat_lit 0) D2M8K2.t7211 from rfl, allE_node, rows7210, irow7204, rows7211]
  all_goals rfl

theorem atot7204 : totK PD2M8K2 D2M8K2.u7204 = [0, 0, 247068692892, 735104092506, 608541477472, 182681217803, 12544355448, 0] := by
  rw [show D2M8K2.u7204 = KTree.node D2M8K2.t7210 (nat_lit 15178837) (nat_lit 1269065816) (nat_lit 0) D2M8K2.t7211 from rfl, totK_node, tot7210, tot7211]
  decide +kernel

theorem arows7206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7206 = true := by
  rw [show D2M8K2.u7206 = KTree.node D2M8K2.t7212 (nat_lit 15180337) (nat_lit 1538198295) (nat_lit 0) D2M8K2.t7213 from rfl, allE_node, rows7212, irow7206, rows7213]
  all_goals rfl

theorem atot7206 : totK PD2M8K2 D2M8K2.u7206 = [0, 0, 188816770458, 761435812035, 717478544120, 119340074925, 1369150432, 0] := by
  rw [show D2M8K2.u7206 = KTree.node D2M8K2.t7212 (nat_lit 15180337) (nat_lit 1538198295) (nat_lit 0) D2M8K2.t7213 from rfl, totK_node, tot7212, tot7213]
  decide +kernel

theorem arows7207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7207 = true := by
  rw [show D2M8K2.u7207 = KTree.node D2M8K2.t7214 (nat_lit 15185824) (nat_lit 2821506518) (nat_lit 0) D2M8K2.t7215 from rfl, allE_node, rows7214, irow7207, rows7215]
  all_goals rfl

theorem atot7207 : totK PD2M8K2 D2M8K2.u7207 = [0, 0, 246735405169, 836392529257, 662187455085, 63645555741, 0, 0] := by
  rw [show D2M8K2.u7207 = KTree.node D2M8K2.t7214 (nat_lit 15185824) (nat_lit 2821506518) (nat_lit 0) D2M8K2.t7215 from rfl, totK_node, tot7214, tot7215]
  decide +kernel

theorem arows7211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7211 = true := by
  rw [show D2M8K2.u7211 = KTree.node D2M8K2.t7216 (nat_lit 15187392) (nat_lit 3757117624) (nat_lit 0) D2M8K2.t7217 from rfl, allE_node, rows7216, irow7211, rows7217]
  all_goals rfl

theorem atot7211 : totK PD2M8K2 D2M8K2.u7211 = [0, 0, 168882656096, 693784623872, 750048534119, 153465736073, 3499003824, 0] := by
  rw [show D2M8K2.u7211 = KTree.node D2M8K2.t7216 (nat_lit 15187392) (nat_lit 3757117624) (nat_lit 0) D2M8K2.t7217 from rfl, totK_node, tot7216, tot7217]
  decide +kernel

theorem arows7212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7212 = true := by
  rw [show D2M8K2.u7212 = KTree.node D2M8K2.t7218 (nat_lit 15189245) (nat_lit 2135832880) (nat_lit 0) D2M8K2.t7219 from rfl, allE_node, rows7218, irow7212, rows7219]
  all_goals rfl

theorem atot7212 : totK PD2M8K2 D2M8K2.u7212 = [0, 0, 259780669291, 750737626160, 608594672600, 126664680799, 7228027050, 0] := by
  rw [show D2M8K2.u7212 = KTree.node D2M8K2.t7218 (nat_lit 15189245) (nat_lit 2135832880) (nat_lit 0) D2M8K2.t7219 from rfl, totK_node, tot7218, tot7219]
  decide +kernel

theorem arows7214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7214 = true := by
  rw [show D2M8K2.u7214 = KTree.node D2M8K2.t7220 (nat_lit 15190945) (nat_lit 1503344942) (nat_lit 0) D2M8K2.t7221 from rfl, allE_node, rows7220, irow7214, rows7221]
  all_goals rfl

theorem atot7214 : totK PD2M8K2 D2M8K2.u7214 = [0, 0, 134395582739, 747741930672, 767870783062, 104664747924, 1198073392, 0] := by
  rw [show D2M8K2.u7214 = KTree.node D2M8K2.t7220 (nat_lit 15190945) (nat_lit 1503344942) (nat_lit 0) D2M8K2.t7221 from rfl, totK_node, tot7220, tot7221]
  decide +kernel

theorem arows7215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7215 = true := by
  rw [show D2M8K2.u7215 = KTree.node D2M8K2.t7222 (nat_lit 15193195) (nat_lit 1348991034) (nat_lit 0) D2M8K2.t7223 from rfl, allE_node, rows7222, irow7215, rows7223]
  all_goals rfl

theorem atot7215 : totK PD2M8K2 D2M8K2.u7215 = [0, 0, 364559950147, 885061549798, 460404375850, 34426055941, 0, 0] := by
  rw [show D2M8K2.u7215 = KTree.node D2M8K2.t7222 (nat_lit 15193195) (nat_lit 1348991034) (nat_lit 0) D2M8K2.t7223 from rfl, totK_node, tot7222, tot7223]
  decide +kernel

theorem arows7218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7218 = true := by
  rw [show D2M8K2.u7218 = KTree.node D2M8K2.t7224 (nat_lit 15194912) (nat_lit 3734875990) (nat_lit 0) D2M8K2.t7225 from rfl, allE_node, rows7224, irow7218, rows7225]
  all_goals rfl

theorem atot7218 : totK PD2M8K2 D2M8K2.u7218 = [0, 0, 88064220118, 631251994004, 858065064283, 165730877140, 4934531535, 0] := by
  rw [show D2M8K2.u7218 = KTree.node D2M8K2.t7224 (nat_lit 15194912) (nat_lit 3734875990) (nat_lit 0) D2M8K2.t7225 from rfl, totK_node, tot7224, tot7225]
  decide +kernel

theorem arows7219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7219 = true := by
  rw [show D2M8K2.u7219 = KTree.node D2M8K2.t7226 (nat_lit 15196809) (nat_lit 1692093122) (nat_lit 0) D2M8K2.t7227 from rfl, allE_node, rows7226, irow7219, rows7227]
  all_goals rfl

theorem atot7219 : totK PD2M8K2 D2M8K2.u7219 = [0, 0, 365686060219, 937475934599, 469457906471, 23361456921, 0, 0] := by
  rw [show D2M8K2.u7219 = KTree.node D2M8K2.t7226 (nat_lit 15196809) (nat_lit 1692093122) (nat_lit 0) D2M8K2.t7227 from rfl, totK_node, tot7226, tot7227]
  decide +kernel

theorem arows7221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7221 = true := by
  rw [show D2M8K2.u7221 = KTree.node D2M8K2.t7228 (nat_lit 15198528) (nat_lit 3287641892) (nat_lit 0) D2M8K2.t7229 from rfl, allE_node, rows7228, irow7221, rows7229]
  all_goals rfl

theorem atot7221 : totK PD2M8K2 D2M8K2.u7221 = [0, 0, 0, 506792559047, 964916294648, 279430393571, 13787500332, 0] := by
  rw [show D2M8K2.u7221 = KTree.node D2M8K2.t7228 (nat_lit 15198528) (nat_lit 3287641892) (nat_lit 0) D2M8K2.t7229 from rfl, totK_node, tot7228, tot7229]
  decide +kernel

theorem arows7222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7222 = true := by
  rw [show D2M8K2.u7222 = KTree.node D2M8K2.t7230 (nat_lit 15200505) (nat_lit 1725113201) (nat_lit 0) D2M8K2.t7231 from rfl, allE_node, rows7230, irow7222, rows7231]
  all_goals rfl

theorem atot7222 : totK PD2M8K2 D2M8K2.u7222 = [0, 0, 0, 356472090005, 966202460692, 402867589881, 18437164080, 0] := by
  rw [show D2M8K2.u7222 = KTree.node D2M8K2.t7230 (nat_lit 15200505) (nat_lit 1725113201) (nat_lit 0) D2M8K2.t7231 from rfl, totK_node, tot7230, tot7231]
  decide +kernel

theorem arows7228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7228 = true := by
  rw [show D2M8K2.u7228 = KTree.node D2M8K2.t7232 (nat_lit 15202442) (nat_lit 3182848614) (nat_lit 0) D2M8K2.t7233 from rfl, allE_node, rows7232, irow7228, rows7233]
  all_goals rfl

theorem atot7228 : totK PD2M8K2 D2M8K2.u7228 = [0, 0, 0, 178611860242, 772413309421, 672891813731, 101606363856, 1369150432] := by
  rw [show D2M8K2.u7228 = KTree.node D2M8K2.t7232 (nat_lit 15202442) (nat_lit 3182848614) (nat_lit 0) D2M8K2.t7233 from rfl, totK_node, tot7232, tot7233]
  decide +kernel

theorem arows7229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7229 = true := by
  rw [show D2M8K2.u7229 = KTree.node D2M8K2.t7234 (nat_lit 15207897) (nat_lit 1609014386) (nat_lit 0) D2M8K2.t7235 from rfl, allE_node, rows7234, irow7229, rows7235]
  all_goals rfl

theorem atot7229 : totK PD2M8K2 D2M8K2.u7229 = [0, 0, 0, 420922404201, 945572284236, 354848709292, 22141929093, 0] := by
  rw [show D2M8K2.u7229 = KTree.node D2M8K2.t7234 (nat_lit 15207897) (nat_lit 1609014386) (nat_lit 0) D2M8K2.t7235 from rfl, totK_node, tot7234, tot7235]
  decide +kernel

theorem arows7231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7231 = true := by
  rw [show D2M8K2.u7231 = KTree.node D2M8K2.t7236 (nat_lit 15213456) (nat_lit 3734880604) (nat_lit 0) D2M8K2.t7237 from rfl, allE_node, rows7236, irow7231, rows7237]
  all_goals rfl

theorem atot7231 : totK PD2M8K2 D2M8K2.u7231 = [0, 0, 0, 490505738744, 973523175313, 263911888836, 10687190963, 0] := by
  rw [show D2M8K2.u7231 = KTree.node D2M8K2.t7236 (nat_lit 15213456) (nat_lit 3734880604) (nat_lit 0) D2M8K2.t7237 from rfl, totK_node, tot7236, tot7237]
  decide +kernel

theorem arows7232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7232 = true := by
  rw [show D2M8K2.u7232 = KTree.node D2M8K2.t7238 (nat_lit 15216968) (nat_lit 3158190354) (nat_lit 0) D2M8K2.t7239 from rfl, allE_node, rows7238, irow7232, rows7239]
  all_goals rfl

theorem atot7232 : totK PD2M8K2 D2M8K2.u7232 = [0, 0, 0, 461379738434, 992736265829, 300092801398, 10264590586, 0] := by
  rw [show D2M8K2.u7232 = KTree.node D2M8K2.t7238 (nat_lit 15216968) (nat_lit 3158190354) (nat_lit 0) D2M8K2.t7239 from rfl, totK_node, tot7238, tot7239]
  decide +kernel

theorem arows7235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7235 = true := by
  rw [show D2M8K2.u7235 = KTree.node D2M8K2.t7240 (nat_lit 15262372) (nat_lit 3848549526) (nat_lit 0) D2M8K2.t7241 from rfl, allE_node, rows7240, irow7235, rows7241]
  all_goals rfl

theorem atot7235 : totK PD2M8K2 D2M8K2.u7235 = [0, 0, 331522328064, 828145270233, 497516647610, 111702102088, 8932028497, 0] := by
  rw [show D2M8K2.u7235 = KTree.node D2M8K2.t7240 (nat_lit 15262372) (nat_lit 3848549526) (nat_lit 0) D2M8K2.t7241 from rfl, totK_node, tot7240, tot7241]
  decide +kernel

theorem arows7236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7236 = true := by
  rw [show D2M8K2.u7236 = KTree.node D2M8K2.t7242 (nat_lit 15263620) (nat_lit 3828483055) (nat_lit 0) D2M8K2.t7243 from rfl, allE_node, rows7242, irow7236, rows7243]
  all_goals rfl

theorem atot7236 : totK PD2M8K2 D2M8K2.u7236 = [0, 0, 84346306670, 675268536018, 872507413721, 131315394390, 1369150432, 0] := by
  rw [show D2M8K2.u7236 = KTree.node D2M8K2.t7242 (nat_lit 15263620) (nat_lit 3828483055) (nat_lit 0) D2M8K2.t7243 from rfl, totK_node, tot7242, tot7243]
  decide +kernel

theorem arows7238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7238 = true := by
  rw [show D2M8K2.u7238 = KTree.node D2M8K2.t7244 (nat_lit 15265973) (nat_lit 2309202145) (nat_lit 0) D2M8K2.t7245 from rfl, allE_node, rows7244, irow7238, rows7245]
  all_goals rfl

theorem atot7238 : totK PD2M8K2 D2M8K2.u7238 = [0, 0, 345168067437, 924037037347, 537158391048, 46928901968, 0, 0] := by
  rw [show D2M8K2.u7238 = KTree.node D2M8K2.t7244 (nat_lit 15265973) (nat_lit 2309202145) (nat_lit 0) D2M8K2.t7245 from rfl, totK_node, tot7244, tot7245]
  decide +kernel

theorem arows7239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7239 = true := by
  rw [show D2M8K2.u7239 = KTree.node D2M8K2.t7246 (nat_lit 15268276) (nat_lit 3692344773) (nat_lit 0) D2M8K2.t7247 from rfl, allE_node, rows7246, irow7239, rows7247]
  all_goals rfl

theorem atot7239 : totK PD2M8K2 D2M8K2.u7239 = [0, 0, 172341156901, 697222418731, 758015747235, 185187111175, 5284349065, 0] := by
  rw [show D2M8K2.u7239 = KTree.node D2M8K2.t7246 (nat_lit 15268276) (nat_lit 3692344773) (nat_lit 0) D2M8K2.t7247 from rfl, totK_node, tot7246, tot7247]
  decide +kernel

theorem arows7243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7243 = true := by
  rw [show D2M8K2.u7243 = KTree.node D2M8K2.t7248 (nat_lit 15269915) (nat_lit 1200934973) (nat_lit 0) D2M8K2.t7249 from rfl, allE_node, rows7248, irow7243, rows7249]
  all_goals rfl

theorem atot7243 : totK PD2M8K2 D2M8K2.u7243 = [0, 0, 266854384785, 833180360151, 626429608844, 79749491497, 1164319620, 0] := by
  rw [show D2M8K2.u7243 = KTree.node D2M8K2.t7248 (nat_lit 15269915) (nat_lit 1200934973) (nat_lit 0) D2M8K2.t7249 from rfl, totK_node, tot7248, tot7249]
  decide +kernel

theorem arows7244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7244 = true := by
  rw [show D2M8K2.u7244 = KTree.node D2M8K2.t7250 (nat_lit 15271569) (nat_lit 1841292011) (nat_lit 0) D2M8K2.t7251 from rfl, allE_node, rows7250, irow7244, rows7251]
  all_goals rfl

theorem atot7244 : totK PD2M8K2 D2M8K2.u7244 = [0, 0, 103791020940, 589919721440, 836826360523, 238045591102, 11885407614, 0] := by
  rw [show D2M8K2.u7244 = KTree.node D2M8K2.t7250 (nat_lit 15271569) (nat_lit 1841292011) (nat_lit 0) D2M8K2.t7251 from rfl, totK_node, tot7250, tot7251]
  decide +kernel

theorem arows7246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7246 = true := by
  rw [show D2M8K2.u7246 = KTree.node D2M8K2.t7252 (nat_lit 15276457) (nat_lit 1476156636) (nat_lit 0) D2M8K2.t7253 from rfl, allE_node, rows7252, irow7246, rows7253]
  all_goals rfl

theorem atot7246 : totK PD2M8K2 D2M8K2.u7246 = [0, 0, 304053746861, 873793643327, 554837179957, 44676176800, 0, 0] := by
  rw [show D2M8K2.u7246 = KTree.node D2M8K2.t7252 (nat_lit 15276457) (nat_lit 1476156636) (nat_lit 0) D2M8K2.t7253 from rfl, totK_node, tot7252, tot7253]
  decide +kernel

theorem arows7247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7247 = true := by
  rw [show D2M8K2.u7247 = KTree.node D2M8K2.t7254 (nat_lit 15278474) (nat_lit 3748610401) (nat_lit 0) D2M8K2.t7255 from rfl, allE_node, rows7254, irow7247, rows7255]
  all_goals rfl

theorem atot7247 : totK PD2M8K2 D2M8K2.u7247 = [0, 0, 165125535034, 681903624369, 767297238197, 157908587424, 4917269347, 0] := by
  rw [show D2M8K2.u7247 = KTree.node D2M8K2.t7254 (nat_lit 15278474) (nat_lit 3748610401) (nat_lit 0) D2M8K2.t7255 from rfl, totK_node, tot7254, tot7255]
  decide +kernel

theorem arows7250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7250 = true := by
  rw [show D2M8K2.u7250 = KTree.node D2M8K2.t7256 (nat_lit 15280436) (nat_lit 2503328268) (nat_lit 0) D2M8K2.t7257 from rfl, allE_node, rows7256, irow7250, rows7257]
  all_goals rfl

theorem atot7250 : totK PD2M8K2 D2M8K2.u7250 = [0, 0, 246519588468, 783240947651, 678316218892, 101061421539, 1232398321, 0] := by
  rw [show D2M8K2.u7250 = KTree.node D2M8K2.t7256 (nat_lit 15280436) (nat_lit 2503328268) (nat_lit 0) D2M8K2.t7257 from rfl, totK_node, tot7256, tot7257]
  decide +kernel

theorem arows7251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7251 = true := by
  rw [show D2M8K2.u7251 = KTree.node D2M8K2.t7258 (nat_lit 15282299) (nat_lit 2876038074) (nat_lit 0) D2M8K2.t7259 from rfl, allE_node, rows7258, irow7251, rows7259]
  all_goals rfl

theorem atot7251 : totK PD2M8K2 D2M8K2.u7251 = [0, 0, 160226755552, 677001961215, 727413570032, 199397049754, 12451903996, 0] := by
  rw [show D2M8K2.u7251 = KTree.node D2M8K2.t7258 (nat_lit 15282299) (nat_lit 2876038074) (nat_lit 0) D2M8K2.t7259 from rfl, totK_node, tot7258, tot7259]
  decide +kernel

theorem arows7253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7253 = true := by
  rw [show D2M8K2.u7253 = KTree.node D2M8K2.t7260 (nat_lit 15304628) (nat_lit 2667416066) (nat_lit 0) D2M8K2.t7261 from rfl, allE_node, rows7260, irow7253, rows7261]
  all_goals rfl

theorem atot7253 : totK PD2M8K2 D2M8K2.u7253 = [0, 0, 256569397827, 795342990758, 621845091241, 96246307687, 1369150432, 0] := by
  rw [show D2M8K2.u7253 = KTree.node D2M8K2.t7260 (nat_lit 15304628) (nat_lit 2667416066) (nat_lit 0) D2M8K2.t7261 from rfl, totK_node, tot7260, tot7261]
  decide +kernel

theorem arows7254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7254 = true := by
  rw [show D2M8K2.u7254 = KTree.node D2M8K2.t7262 (nat_lit 15313646) (nat_lit 2975112356) (nat_lit 0) D2M8K2.t7263 from rfl, allE_node, rows7262, irow7254, rows7263]
  all_goals rfl

theorem atot7254 : totK PD2M8K2 D2M8K2.u7254 = [0, 0, 253160358258, 849281057813, 652901686168, 54247570883, 0, 0] := by
  rw [show D2M8K2.u7254 = KTree.node D2M8K2.t7262 (nat_lit 15313646) (nat_lit 2975112356) (nat_lit 0) D2M8K2.t7263 from rfl, totK_node, tot7262, tot7263]
  decide +kernel

theorem arows7259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7259 = true := by
  rw [show D2M8K2.u7259 = KTree.node D2M8K2.t7264 (nat_lit 15315181) (nat_lit 979199521) (nat_lit 0) D2M8K2.t7265 from rfl, allE_node, rows7264, irow7259, rows7265]
  all_goals rfl

theorem atot7259 : totK PD2M8K2 D2M8K2.u7259 = [0, 0, 351547289786, 932920422985, 479522076610, 28305136031, 0, 0] := by
  rw [show D2M8K2.u7259 = KTree.node D2M8K2.t7264 (nat_lit 15315181) (nat_lit 979199521) (nat_lit 0) D2M8K2.t7265 from rfl, totK_node, tot7264, tot7265]
  decide +kernel

theorem arows7260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7260 = true := by
  rw [show D2M8K2.u7260 = KTree.node D2M8K2.t7266 (nat_lit 15318230) (nat_lit 3901408561) (nat_lit 0) D2M8K2.t7267 from rfl, allE_node, rows7266, irow7260, rows7267]
  all_goals rfl

theorem atot7260 : totK PD2M8K2 D2M8K2.u7260 = [0, 0, 213112947318, 798026777579, 652161874522, 82805444312, 1096505104, 0] := by
  rw [show D2M8K2.u7260 = KTree.node D2M8K2.t7266 (nat_lit 15318230) (nat_lit 3901408561) (nat_lit 0) D2M8K2.t7267 from rfl, totK_node, tot7266, tot7267]
  decide +kernel

theorem arows7262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7262 = true := by
  rw [show D2M8K2.u7262 = KTree.node D2M8K2.t7268 (nat_lit 15320800) (nat_lit 3585136352) (nat_lit 0) D2M8K2.t7269 from rfl, allE_node, rows7268, irow7262, rows7269]
  all_goals rfl

theorem atot7262 : totK PD2M8K2 D2M8K2.u7262 = [0, 0, 321730702709, 888772473389, 570447260773, 44892777363, 0, 0] := by
  rw [show D2M8K2.u7262 = KTree.node D2M8K2.t7268 (nat_lit 15320800) (nat_lit 3585136352) (nat_lit 0) D2M8K2.t7269 from rfl, totK_node, tot7268, tot7269]
  decide +kernel

theorem arows7263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7263 = true := by
  rw [show D2M8K2.u7263 = KTree.node D2M8K2.t7270 (nat_lit 15345236) (nat_lit 3217724190) (nat_lit 0) D2M8K2.t7271 from rfl, allE_node, rows7270, irow7263, rows7271]
  all_goals rfl

theorem atot7263 : totK PD2M8K2 D2M8K2.u7263 = [0, 0, 370078997046, 922776148657, 451950758092, 32083862920, 0, 0] := by
  rw [show D2M8K2.u7263 = KTree.node D2M8K2.t7270 (nat_lit 15345236) (nat_lit 3217724190) (nat_lit 0) D2M8K2.t7271 from rfl, totK_node, tot7270, tot7271]
  decide +kernel

theorem arows7266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7266 = true := by
  rw [show D2M8K2.u7266 = KTree.node D2M8K2.t7272 (nat_lit 15346484) (nat_lit 3476848073) (nat_lit 0) D2M8K2.t7273 from rfl, allE_node, rows7272, irow7266, rows7273]
  all_goals rfl

theorem atot7266 : totK PD2M8K2 D2M8K2.u7266 = [0, 0, 123153304415, 700809903000, 802977997862, 127814014600, 1369150432, 0] := by
  rw [show D2M8K2.u7266 = KTree.node D2M8K2.t7272 (nat_lit 15346484) (nat_lit 3476848073) (nat_lit 0) D2M8K2.t7273 from rfl, totK_node, tot7272, tot7273]
  decide +kernel

theorem arows7267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7267 = true := by
  rw [show D2M8K2.u7267 = KTree.node D2M8K2.t7274 (nat_lit 15348849) (nat_lit 1582527424) (nat_lit 0) D2M8K2.t7275 from rfl, allE_node, rows7274, irow7267, rows7275]
  all_goals rfl

theorem atot7267 : totK PD2M8K2 D2M8K2.u7267 = [0, 0, 327904710154, 914985176438, 534794979599, 39588085479, 0, 0] := by
  rw [show D2M8K2.u7267 = KTree.node D2M8K2.t7274 (nat_lit 15348849) (nat_lit 1582527424) (nat_lit 0) D2M8K2.t7275 from rfl, totK_node, tot7274, tot7275]
  decide +kernel

theorem arows7269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7269 = true := by
  rw [show D2M8K2.u7269 = KTree.node D2M8K2.t7276 (nat_lit 15351564) (nat_lit 3603685625) (nat_lit 0) D2M8K2.t7277 from rfl, allE_node, rows7276, irow7269, rows7277]
  all_goals rfl

theorem atot7269 : totK PD2M8K2 D2M8K2.u7269 = [0, 0, 204884860792, 780106477326, 714809061046, 105925505568, 1409560813, 0] := by
  rw [show D2M8K2.u7269 = KTree.node D2M8K2.t7276 (nat_lit 15351564) (nat_lit 3603685625) (nat_lit 0) D2M8K2.t7277 from rfl, totK_node, tot7276, tot7277]
  decide +kernel

theorem arows7270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7270 = true := by
  rw [show D2M8K2.u7270 = KTree.node D2M8K2.t7278 (nat_lit 15353114) (nat_lit 3808638483) (nat_lit 0) D2M8K2.t7279 from rfl, allE_node, rows7278, irow7270, rows7279]
  all_goals rfl

theorem atot7270 : totK PD2M8K2 D2M8K2.u7270 = [0, 0, 207066200254, 779422447417, 691263473918, 103612568071, 1164319620, 0] := by
  rw [show D2M8K2.u7270 = KTree.node D2M8K2.t7278 (nat_lit 15353114) (nat_lit 3808638483) (nat_lit 0) D2M8K2.t7279 from rfl, totK_node, tot7278, tot7279]
  decide +kernel

theorem arows7274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7274 = true := by
  rw [show D2M8K2.u7274 = KTree.node D2M8K2.t7280 (nat_lit 15355012) (nat_lit 3441970485) (nat_lit 0) D2M8K2.t7281 from rfl, allE_node, rows7280, irow7274, rows7281]
  all_goals rfl

theorem atot7274 : totK PD2M8K2 D2M8K2.u7274 = [0, 0, 222355793932, 687199425991, 660918850790, 185226792397, 11819130176, 0] := by
  rw [show D2M8K2.u7274 = KTree.node D2M8K2.t7280 (nat_lit 15355012) (nat_lit 3441970485) (nat_lit 0) D2M8K2.t7281 from rfl, totK_node, tot7280, tot7281]
  decide +kernel

theorem arows7275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7275 = true := by
  rw [show D2M8K2.u7275 = KTree.node D2M8K2.t7282 (nat_lit 15356784) (nat_lit 3572150936) (nat_lit 0) D2M8K2.t7283 from rfl, allE_node, rows7282, irow7275, rows7283]
  all_goals rfl

theorem atot7275 : totK PD2M8K2 D2M8K2.u7275 = [0, 0, 155411847315, 764107370289, 750835904584, 88282918359, 1198073392, 0] := by
  rw [show D2M8K2.u7275 = KTree.node D2M8K2.t7282 (nat_lit 15356784) (nat_lit 3572150936) (nat_lit 0) D2M8K2.t7283 from rfl, totK_node, tot7282, tot7283]
  decide +kernel

theorem arows7277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7277 = true := by
  rw [show D2M8K2.u7277 = KTree.node D2M8K2.t7284 (nat_lit 15359045) (nat_lit 2337965196) (nat_lit 0) D2M8K2.t7285 from rfl, allE_node, rows7284, irow7277, rows7285]
  all_goals rfl

theorem atot7277 : totK PD2M8K2 D2M8K2.u7277 = [0, 0, 358897424727, 925422720472, 478613768261, 32649106074, 0, 0] := by
  rw [show D2M8K2.u7277 = KTree.node D2M8K2.t7284 (nat_lit 15359045) (nat_lit 2337965196) (nat_lit 0) D2M8K2.t7285 from rfl, totK_node, tot7284, tot7285]
  decide +kernel

theorem arows7278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7278 = true := by
  rw [show D2M8K2.u7278 = KTree.node D2M8K2.t7286 (nat_lit 15360580) (nat_lit 3777235321) (nat_lit 0) D2M8K2.t7287 from rfl, allE_node, rows7286, irow7278, rows7287]
  all_goals rfl

theorem atot7278 : totK PD2M8K2 D2M8K2.u7278 = [0, 0, 74989312342, 636231714107, 907486556388, 167715730330, 2165917952, 0] := by
  rw [show D2M8K2.u7278 = KTree.node D2M8K2.t7286 (nat_lit 15360580) (nat_lit 3777235321) (nat_lit 0) D2M8K2.t7287 from rfl, totK_node, tot7286, tot7287]
  decide +kernel

theorem arows7281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7281 = true := by
  rw [show D2M8K2.u7281 = KTree.node D2M8K2.t7288 (nat_lit 15386998) (nat_lit 3496872286) (nat_lit 0) D2M8K2.t7289 from rfl, allE_node, rows7288, irow7281, rows7289]
  all_goals rfl

theorem atot7281 : totK PD2M8K2 D2M8K2.u7281 = [0, 0, 396430171358, 933500842046, 399357927976, 33242050222, 2814597007, 0] := by
  rw [show D2M8K2.u7281 = KTree.node D2M8K2.t7288 (nat_lit 15386998) (nat_lit 3496872286) (nat_lit 0) D2M8K2.t7289 from rfl, totK_node, tot7288, tot7289]
  decide +kernel

theorem arows7282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7282 = true := by
  rw [show D2M8K2.u7282 = KTree.node D2M8K2.t7290 (nat_lit 15388705) (nat_lit 1561875799) (nat_lit 0) D2M8K2.t7291 from rfl, allE_node, rows7290, irow7282, rows7291]
  all_goals rfl

theorem atot7282 : totK PD2M8K2 D2M8K2.u7282 = [0, 0, 108755018789, 696032133016, 860529518057, 139952437109, 1369150432, 0] := by
  rw [show D2M8K2.u7282 = KTree.node D2M8K2.t7290 (nat_lit 15388705) (nat_lit 1561875799) (nat_lit 0) D2M8K2.t7291 from rfl, totK_node, tot7290, tot7291]
  decide +kernel

theorem arows7284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7284 = true := by
  rw [show D2M8K2.u7284 = KTree.node D2M8K2.t7292 (nat_lit 15390670) (nat_lit 3023972472) (nat_lit 0) D2M8K2.t7293 from rfl, allE_node, rows7292, irow7284, rows7293]
  all_goals rfl

theorem atot7284 : totK PD2M8K2 D2M8K2.u7284 = [0, 0, 342816261978, 914955060682, 524849702892, 45031168126, 0, 0] := by
  rw [show D2M8K2.u7284 = KTree.node D2M8K2.t7292 (nat_lit 15390670) (nat_lit 3023972472) (nat_lit 0) D2M8K2.t7293 from rfl, totK_node, tot7292, tot7293]
  decide +kernel

theorem arows7285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7285 = true := by
  rw [show D2M8K2.u7285 = KTree.node D2M8K2.t7294 (nat_lit 15394189) (nat_lit 1379464656) (nat_lit 0) D2M8K2.t7295 from rfl, allE_node, rows7294, irow7285, rows7295]
  all_goals rfl

theorem atot7285 : totK PD2M8K2 D2M8K2.u7285 = [0, 0, 313736710971, 897153682175, 562311774345, 47578675767, 0, 0] := by
  rw [show D2M8K2.u7285 = KTree.node D2M8K2.t7294 (nat_lit 15394189) (nat_lit 1379464656) (nat_lit 0) D2M8K2.t7295 from rfl, totK_node, tot7294, tot7295]
  decide +kernel

theorem arows7292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7292 = true := by
  rw [show D2M8K2.u7292 = KTree.node D2M8K2.t7296 (nat_lit 15395953) (nat_lit 1452498880) (nat_lit 0) D2M8K2.t7297 from rfl, allE_node, rows7296, irow7292, rows7297]
  all_goals rfl

theorem atot7292 : totK PD2M8K2 D2M8K2.u7292 = [0, 0, 151182405642, 673903229916, 803415531698, 182036436678, 5138457373, 0] := by
  rw [show D2M8K2.u7292 = KTree.node D2M8K2.t7296 (nat_lit 15395953) (nat_lit 1452498880) (nat_lit 0) D2M8K2.t7297 from rfl, totK_node, tot7296, tot7297]
  decide +kernel

theorem arows7293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7293 = true := by
  rw [show D2M8K2.u7293 = KTree.node D2M8K2.t7298 (nat_lit 15398006) (nat_lit 3930760718) (nat_lit 0) D2M8K2.t7299 from rfl, allE_node, rows7298, irow7293, rows7299]
  all_goals rfl

theorem atot7293 : totK PD2M8K2 D2M8K2.u7293 = [0, 0, 401977080812, 929090121188, 462045769020, 32440234775, 0, 0] := by
  rw [show D2M8K2.u7293 = KTree.node D2M8K2.t7298 (nat_lit 15398006) (nat_lit 3930760718) (nat_lit 0) D2M8K2.t7299 from rfl, totK_node, tot7298, tot7299]
  decide +kernel

theorem arows7295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7295 = true := by
  rw [show D2M8K2.u7295 = KTree.node D2M8K2.t7300 (nat_lit 15404400) (nat_lit 3670924747) (nat_lit 0) D2M8K2.t7301 from rfl, allE_node, rows7300, irow7295, rows7301]
  all_goals rfl

theorem atot7295 : totK PD2M8K2 D2M8K2.u7295 = [0, 0, 266680067911, 856870531567, 640631475172, 61741648496, 0, 0] := by
  rw [show D2M8K2.u7295 = KTree.node D2M8K2.t7300 (nat_lit 15404400) (nat_lit 3670924747) (nat_lit 0) D2M8K2.t7301 from rfl, totK_node, tot7300, tot7301]
  decide +kernel

theorem arows7296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7296 = true := by
  rw [show D2M8K2.u7296 = KTree.node D2M8K2.t7302 (nat_lit 15406566) (nat_lit 3754526149) (nat_lit 0) D2M8K2.t7303 from rfl, allE_node, rows7302, irow7296, rows7303]
  all_goals rfl

theorem atot7296 : totK PD2M8K2 D2M8K2.u7296 = [0, 94445126902, 239990604536, 498447203307, 729255642403, 253960128887, 13864292063, 0] := by
  rw [show D2M8K2.u7296 = KTree.node D2M8K2.t7302 (nat_lit 15406566) (nat_lit 3754526149) (nat_lit 0) D2M8K2.t7303 from rfl, totK_node, tot7302, tot7303]
  decide +kernel

theorem arows7299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7299 = true := by
  rw [show D2M8K2.u7299 = KTree.node D2M8K2.t7304 (nat_lit 15473668) (nat_lit 3551038512) (nat_lit 0) D2M8K2.t7305 from rfl, allE_node, rows7304, irow7299, rows7305]
  all_goals rfl

theorem atot7299 : totK PD2M8K2 D2M8K2.u7299 = [0, 354984806307, 930171613438, 514973875830, 40769088700, 0, 0, 0] := by
  rw [show D2M8K2.u7299 = KTree.node D2M8K2.t7304 (nat_lit 15473668) (nat_lit 3551038512) (nat_lit 0) D2M8K2.t7305 from rfl, totK_node, tot7304, tot7305]
  decide +kernel

theorem arows7300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7300 = true := by
  rw [show D2M8K2.u7300 = KTree.node D2M8K2.t7306 (nat_lit 15475115) (nat_lit 2333040258) (nat_lit 0) D2M8K2.t7307 from rfl, allE_node, rows7306, irow7300, rows7307]
  all_goals rfl

theorem atot7300 : totK PD2M8K2 D2M8K2.u7300 = [0, 0, 390074901843, 945535561126, 451930997397, 30804453458, 0, 0] := by
  rw [show D2M8K2.u7300 = KTree.node D2M8K2.t7306 (nat_lit 15475115) (nat_lit 2333040258) (nat_lit 0) D2M8K2.t7307 from rfl, totK_node, tot7306, tot7307]
  decide +kernel

theorem arows7302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7302 = true := by
  rw [show D2M8K2.u7302 = KTree.node D2M8K2.t7308 (nat_lit 15476441) (nat_lit 1700818347) (nat_lit 0) D2M8K2.t7309 from rfl, allE_node, rows7308, irow7302, rows7309]
  all_goals rfl

theorem atot7302 : totK PD2M8K2 D2M8K2.u7302 = [0, 335948435649, 817303065411, 539429746342, 134914508188, 6804944647, 0, 0] := by
  rw [show D2M8K2.u7302 = KTree.node D2M8K2.t7308 (nat_lit 15476441) (nat_lit 1700818347) (nat_lit 0) D2M8K2.t7309 from rfl, totK_node, tot7308, tot7309]
  decide +kernel

theorem arows7303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7303 = true := by
  rw [show D2M8K2.u7303 = KTree.node D2M8K2.t7310 (nat_lit 15477966) (nat_lit 2918818048) (nat_lit 0) D2M8K2.t7311 from rfl, allE_node, rows7310, irow7303, rows7311]
  all_goals rfl

theorem atot7303 : totK PD2M8K2 D2M8K2.u7303 = [0, 87489962043, 636693387915, 860285954453, 206488171520, 8402921910, 0, 0] := by
  rw [show D2M8K2.u7303 = KTree.node D2M8K2.t7310 (nat_lit 15477966) (nat_lit 2918818048) (nat_lit 0) D2M8K2.t7311 from rfl, totK_node, tot7310, tot7311]
  decide +kernel

theorem arows7307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7307 = true := by
  rw [show D2M8K2.u7307 = KTree.node D2M8K2.t7312 (nat_lit 15479882) (nat_lit 4267463172) (nat_lit 0) D2M8K2.t7313 from rfl, allE_node, rows7312, irow7307, rows7313]
  all_goals rfl

theorem atot7307 : totK PD2M8K2 D2M8K2.u7307 = [0, 310028926791, 799525645439, 585176258848, 113317949333, 3434488093, 0, 0] := by
  rw [show D2M8K2.u7307 = KTree.node D2M8K2.t7312 (nat_lit 15479882) (nat_lit 4267463172) (nat_lit 0) D2M8K2.t7313 from rfl, totK_node, tot7312, tot7313]
  decide +kernel

theorem arows7308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7308 = true := by
  rw [show D2M8K2.u7308 = KTree.node D2M8K2.t7314 (nat_lit 15481473) (nat_lit 1765856112) (nat_lit 0) D2M8K2.t7315 from rfl, allE_node, rows7314, irow7308, rows7315]
  all_goals rfl

theorem atot7308 : totK PD2M8K2 D2M8K2.u7308 = [0, 90498161130, 644204367386, 842085765808, 200709645227, 6860571838, 0, 0] := by
  rw [show D2M8K2.u7308 = KTree.node D2M8K2.t7314 (nat_lit 15481473) (nat_lit 1765856112) (nat_lit 0) D2M8K2.t7315 from rfl, totK_node, tot7314, tot7315]
  decide +kernel

theorem arows7310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7310 = true := by
  rw [show D2M8K2.u7310 = KTree.node D2M8K2.t7316 (nat_lit 15483284) (nat_lit 3684646199) (nat_lit 0) D2M8K2.t7317 from rfl, allE_node, rows7316, irow7310, rows7317]
  all_goals rfl

theorem atot7310 : totK PD2M8K2 D2M8K2.u7310 = [0, 312217536150, 800672117722, 571576249702, 113576767582, 2348208889, 0, 0] := by
  rw [show D2M8K2.u7310 = KTree.node D2M8K2.t7316 (nat_lit 15483284) (nat_lit 3684646199) (nat_lit 0) D2M8K2.t7317 from rfl, totK_node, tot7316, tot7317]
  decide +kernel

theorem arows7311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7311 = true := by
  rw [show D2M8K2.u7311 = KTree.node D2M8K2.t7318 (nat_lit 15484809) (nat_lit 1711007923) (nat_lit 0) D2M8K2.t7319 from rfl, allE_node, rows7318, irow7311, rows7319]
  all_goals rfl

theorem atot7311 : totK PD2M8K2 D2M8K2.u7311 = [0, 105375231182, 729049209300, 847920224874, 118444291750, 0, 0, 0] := by
  rw [show D2M8K2.u7311 = KTree.node D2M8K2.t7318 (nat_lit 15484809) (nat_lit 1711007923) (nat_lit 0) D2M8K2.t7319 from rfl, totK_node, tot7318, tot7319]
  decide +kernel

theorem arows7314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7314 = true := by
  rw [show D2M8K2.u7314 = KTree.node D2M8K2.t7320 (nat_lit 15486824) (nat_lit 3480628914) (nat_lit 0) D2M8K2.t7321 from rfl, allE_node, rows7320, irow7314, rows7321]
  all_goals rfl

theorem atot7314 : totK PD2M8K2 D2M8K2.u7314 = [0, 330124442722, 824554081213, 542105959326, 107979636148, 3867150671, 0, 0] := by
  rw [show D2M8K2.u7314 = KTree.node D2M8K2.t7320 (nat_lit 15486824) (nat_lit 3480628914) (nat_lit 0) D2M8K2.t7321 from rfl, totK_node, tot7320, tot7321]
  decide +kernel

theorem arows7315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7315 = true := by
  rw [show D2M8K2.u7315 = KTree.node D2M8K2.t7322 (nat_lit 15488332) (nat_lit 3698045791) (nat_lit 0) D2M8K2.t7323 from rfl, allE_node, rows7322, irow7315, rows7323]
  all_goals rfl

theorem atot7315 : totK PD2M8K2 D2M8K2.u7315 = [0, 92759131966, 625016541454, 861914377156, 211917089692, 4929677829, 0, 0] := by
  rw [show D2M8K2.u7315 = KTree.node D2M8K2.t7322 (nat_lit 15488332) (nat_lit 3698045791) (nat_lit 0) D2M8K2.t7323 from rfl, totK_node, tot7322, tot7323]
  decide +kernel

theorem arows7317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7317 = true := by
  rw [show D2M8K2.u7317 = KTree.node D2M8K2.t7324 (nat_lit 15493706) (nat_lit 4274136801) (nat_lit 0) D2M8K2.t7325 from rfl, allE_node, rows7324, irow7317, rows7325]
  all_goals rfl

theorem atot7317 : totK PD2M8K2 D2M8K2.u7317 = [0, 0, 363060999394, 915934190273, 502686663717, 44039675282, 0, 0] := by
  rw [show D2M8K2.u7317 = KTree.node D2M8K2.t7324 (nat_lit 15493706) (nat_lit 4274136801) (nat_lit 0) D2M8K2.t7325 from rfl, totK_node, tot7324, tot7325]
  decide +kernel

theorem arows7318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7318 = true := by
  rw [show D2M8K2.u7318 = KTree.node D2M8K2.t7326 (nat_lit 15494863) (nat_lit 2205373273) (nat_lit 0) D2M8K2.t7327 from rfl, allE_node, rows7326, irow7318, rows7327]
  all_goals rfl

theorem atot7318 : totK PD2M8K2 D2M8K2.u7318 = [0, 0, 177099220112, 727899770609, 699427704846, 204496882248, 21385604922, 0] := by
  rw [show D2M8K2.u7318 = KTree.node D2M8K2.t7326 (nat_lit 15494863) (nat_lit 2205373273) (nat_lit 0) D2M8K2.t7327 from rfl, totK_node, tot7326, tot7327]
  decide +kernel

theorem arows7323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7323 = true := by
  rw [show D2M8K2.u7323 = KTree.node D2M8K2.t7328 (nat_lit 15496353) (nat_lit 1746752022) (nat_lit 0) D2M8K2.t7329 from rfl, allE_node, rows7328, irow7323, rows7329]
  all_goals rfl

theorem atot7323 : totK PD2M8K2 D2M8K2.u7323 = [0, 0, 120817755924, 509908284379, 793022955291, 345338024553, 15536268932, 0] := by
  rw [show D2M8K2.u7323 = KTree.node D2M8K2.t7328 (nat_lit 15496353) (nat_lit 1746752022) (nat_lit 0) D2M8K2.t7329 from rfl, totK_node, tot7328, tot7329]
  decide +kernel

theorem arows7324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7324 = true := by
  rw [show D2M8K2.u7324 = KTree.node D2M8K2.t7330 (nat_lit 15497903) (nat_lit 1988001829) (nat_lit 0) D2M8K2.t7331 from rfl, allE_node, rows7330, irow7324, rows7331]
  all_goals rfl

theorem atot7324 : totK PD2M8K2 D2M8K2.u7324 = [0, 0, 300697644739, 884882583654, 570644111609, 49249181042, 0, 0] := by
  rw [show D2M8K2.u7324 = KTree.node D2M8K2.t7330 (nat_lit 15497903) (nat_lit 1988001829) (nat_lit 0) D2M8K2.t7331 from rfl, totK_node, tot7330, tot7331]
  decide +kernel

theorem arows7326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7326 = true := by
  rw [show D2M8K2.u7326 = KTree.node D2M8K2.t7332 (nat_lit 15499728) (nat_lit 3193284888) (nat_lit 0) D2M8K2.t7333 from rfl, allE_node, rows7332, irow7326, rows7333]
  all_goals rfl

theorem atot7326 : totK PD2M8K2 D2M8K2.u7326 = [0, 0, 141127144203, 659861513370, 807281866128, 204641397715, 5159868635, 0] := by
  rw [show D2M8K2.u7326 = KTree.node D2M8K2.t7332 (nat_lit 15499728) (nat_lit 3193284888) (nat_lit 0) D2M8K2.t7333 from rfl, totK_node, tot7332, tot7333]
  decide +kernel

theorem arows7327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7327 = true := by
  rw [show D2M8K2.u7327 = KTree.node D2M8K2.t7334 (nat_lit 15501484) (nat_lit 3535369598) (nat_lit 0) D2M8K2.t7335 from rfl, allE_node, rows7334, irow7327, rows7335]
  all_goals rfl

theorem atot7327 : totK PD2M8K2 D2M8K2.u7327 = [0, 0, 261320023696, 865697046464, 628528050305, 53892618386, 0, 0] := by
  rw [show D2M8K2.u7327 = KTree.node D2M8K2.t7334 (nat_lit 15501484) (nat_lit 3535369598) (nat_lit 0) D2M8K2.t7335 from rfl, totK_node, tot7334, tot7335]
  decide +kernel

theorem arows7330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7330 = true := by
  rw [show D2M8K2.u7330 = KTree.node D2M8K2.t7336 (nat_lit 15503403) (nat_lit 3612347571) (nat_lit 0) D2M8K2.t7337 from rfl, allE_node, rows7336, irow7330, rows7337]
  all_goals rfl

theorem atot7330 : totK PD2M8K2 D2M8K2.u7330 = [0, 0, 169495686935, 660606060228, 762158453404, 186035867486, 5218872685, 0] := by
  rw [show D2M8K2.u7330 = KTree.node D2M8K2.t7336 (nat_lit 15503403) (nat_lit 3612347571) (nat_lit 0) D2M8K2.t7337 from rfl, totK_node, tot7336, tot7337]
  decide +kernel

theorem arows7331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7331 = true := by
  rw [show D2M8K2.u7331 = KTree.node D2M8K2.t7338 (nat_lit 15504802) (nat_lit 3369326931) (nat_lit 0) D2M8K2.t7339 from rfl, allE_node, rows7338, irow7331, rows7339]
  all_goals rfl

theorem atot7331 : totK PD2M8K2 D2M8K2.u7331 = [0, 0, 246197106849, 858595613678, 635831491727, 54407207925, 0, 0] := by
  rw [show D2M8K2.u7331 = KTree.node D2M8K2.t7338 (nat_lit 15504802) (nat_lit 3369326931) (nat_lit 0) D2M8K2.t7339 from rfl, totK_node, tot7338, tot7339]
  decide +kernel

theorem arows7333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7333 = true := by
  rw [show D2M8K2.u7333 = KTree.node D2M8K2.t7340 (nat_lit 15507220) (nat_lit 3537778823) (nat_lit 0) D2M8K2.t7341 from rfl, allE_node, rows7340, irow7333, rows7341]
  all_goals rfl

theorem atot7333 : totK PD2M8K2 D2M8K2.u7333 = [0, 0, 243286427987, 771375146367, 685748088669, 119839712459, 1415142070, 0] := by
  rw [show D2M8K2.u7333 = KTree.node D2M8K2.t7340 (nat_lit 15507220) (nat_lit 3537778823) (nat_lit 0) D2M8K2.t7341 from rfl, totK_node, tot7340, tot7341]
  decide +kernel

theorem arows7334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7334 = true := by
  rw [show D2M8K2.u7334 = KTree.node D2M8K2.t7342 (nat_lit 15508713) (nat_lit 1349885212) (nat_lit 0) D2M8K2.t7343 from rfl, allE_node, rows7342, irow7334, rows7343]
  all_goals rfl

theorem atot7334 : totK PD2M8K2 D2M8K2.u7334 = [0, 0, 177626494765, 770877365262, 730667387762, 119522419966, 1238673482, 0] := by
  rw [show D2M8K2.u7334 = KTree.node D2M8K2.t7342 (nat_lit 15508713) (nat_lit 1349885212) (nat_lit 0) D2M8K2.t7343 from rfl, totK_node, tot7342, tot7343]
  decide +kernel

theorem arows7338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7338 = true := by
  rw [show D2M8K2.u7338 = KTree.node D2M8K2.t7344 (nat_lit 15510629) (nat_lit 2300618398) (nat_lit 0) D2M8K2.t7345 from rfl, allE_node, rows7344, irow7338, rows7345]
  all_goals rfl

theorem atot7338 : totK PD2M8K2 D2M8K2.u7338 = [0, 257424335988, 571935478240, 363112277204, 413203964831, 171398487267, 8063697217, 0] := by
  rw [show D2M8K2.u7338 = KTree.node D2M8K2.t7344 (nat_lit 15510629) (nat_lit 2300618398) (nat_lit 0) D2M8K2.t7345 from rfl, totK_node, tot7344, tot7345]
  decide +kernel

theorem arows7339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7339 = true := by
  rw [show D2M8K2.u7339 = KTree.node D2M8K2.t7346 (nat_lit 15512480) (nat_lit 3204157090) (nat_lit 0) D2M8K2.t7347 from rfl, allE_node, rows7346, irow7339, rows7347]
  all_goals rfl

theorem atot7339 : totK PD2M8K2 D2M8K2.u7339 = [0, 143308751019, 724193278940, 811658560996, 127956429931, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7339 = KTree.node D2M8K2.t7346 (nat_lit 15512480) (nat_lit 3204157090) (nat_lit 0) D2M8K2.t7347 from rfl, totK_node, tot7346, tot7347]
  decide +kernel

theorem arows7341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7341 = true := by
  rw [show D2M8K2.u7341 = KTree.node D2M8K2.t7348 (nat_lit 15514951) (nat_lit 2369530220) (nat_lit 0) D2M8K2.t7349 from rfl, allE_node, rows7348, irow7341, rows7349]
  all_goals rfl

theorem atot7341 : totK PD2M8K2 D2M8K2.u7341 = [0, 367189792200, 936255277350, 493834195840, 40819355862, 0, 0, 0] := by
  rw [show D2M8K2.u7341 = KTree.node D2M8K2.t7348 (nat_lit 15514951) (nat_lit 2369530220) (nat_lit 0) D2M8K2.t7349 from rfl, totK_node, tot7348, tot7349]
  decide +kernel

theorem arows7342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7342 = true := by
  rw [show D2M8K2.u7342 = KTree.node D2M8K2.t7350 (nat_lit 15516408) (nat_lit 3245526189) (nat_lit 0) D2M8K2.t7351 from rfl, allE_node, rows7350, irow7342, rows7351]
  all_goals rfl

theorem atot7342 : totK PD2M8K2 D2M8K2.u7342 = [0, 0, 421140721747, 941511991170, 419300654144, 29387185185, 0, 0] := by
  rw [show D2M8K2.u7342 = KTree.node D2M8K2.t7350 (nat_lit 15516408) (nat_lit 3245526189) (nat_lit 0) D2M8K2.t7351 from rfl, totK_node, tot7350, tot7351]
  decide +kernel

theorem arows7345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7345 = true := by
  rw [show D2M8K2.u7345 = KTree.node D2M8K2.t7352 (nat_lit 15517767) (nat_lit 3638030424) (nat_lit 0) D2M8K2.t7353 from rfl, allE_node, rows7352, irow7345, rows7353]
  all_goals rfl

theorem atot7345 : totK PD2M8K2 D2M8K2.u7345 = [0, 266112628458, 764407656489, 617502726156, 179081559649, 8209931632, 0, 0] := by
  rw [show D2M8K2.u7345 = KTree.node D2M8K2.t7352 (nat_lit 15517767) (nat_lit 3638030424) (nat_lit 0) D2M8K2.t7353 from rfl, totK_node, tot7352, tot7353]
  decide +kernel

theorem arows7346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7346 = true := by
  rw [show D2M8K2.u7346 = KTree.node D2M8K2.t7354 (nat_lit 15519179) (nat_lit 2883116426) (nat_lit 0) D2M8K2.t7355 from rfl, allE_node, rows7354, irow7346, rows7355]
  all_goals rfl

theorem atot7346 : totK PD2M8K2 D2M8K2.u7346 = [0, 175351648363, 712363753977, 767787398658, 156161882169, 2309606161, 0, 0] := by
  rw [show D2M8K2.u7346 = KTree.node D2M8K2.t7354 (nat_lit 15519179) (nat_lit 2883116426) (nat_lit 0) D2M8K2.t7355 from rfl, totK_node, tot7354, tot7355]
  decide +kernel

theorem arows7348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7348 = true := by
  rw [show D2M8K2.u7348 = KTree.node D2M8K2.t7356 (nat_lit 15524454) (nat_lit 3440535855) (nat_lit 0) D2M8K2.t7357 from rfl, allE_node, rows7356, irow7348, rows7357]
  all_goals rfl

theorem atot7348 : totK PD2M8K2 D2M8K2.u7348 = [0, 246388889887, 717676274446, 652629257758, 174111379718, 10740121073, 0, 0] := by
  rw [show D2M8K2.u7348 = KTree.node D2M8K2.t7356 (nat_lit 15524454) (nat_lit 3440535855) (nat_lit 0) D2M8K2.t7357 from rfl, totK_node, tot7356, tot7357]
  decide +kernel

theorem arows7349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7349 = true := by
  rw [show D2M8K2.u7349 = KTree.node D2M8K2.t7358 (nat_lit 15525698) (nat_lit 3979936580) (nat_lit 0) D2M8K2.t7359 from rfl, allE_node, rows7358, irow7349, rows7359]
  all_goals rfl

theorem atot7349 : totK PD2M8K2 D2M8K2.u7349 = [0, 161374371480, 758689669537, 754497464368, 111232707833, 1096505104, 0, 0] := by
  rw [show D2M8K2.u7349 = KTree.node D2M8K2.t7358 (nat_lit 15525698) (nat_lit 3979936580) (nat_lit 0) D2M8K2.t7359 from rfl, totK_node, tot7358, tot7359]
  decide +kernel

theorem arows7355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7355 = true := by
  rw [show D2M8K2.u7355 = KTree.node D2M8K2.t7360 (nat_lit 15528030) (nat_lit 3248705974) (nat_lit 0) D2M8K2.t7361 from rfl, allE_node, rows7360, irow7355, rows7361]
  all_goals rfl

theorem atot7355 : totK PD2M8K2 D2M8K2.u7355 = [0, 256725865643, 781297352522, 645969539880, 130751669846, 3884009855, 0, 0] := by
  rw [show D2M8K2.u7355 = KTree.node D2M8K2.t7360 (nat_lit 15528030) (nat_lit 3248705974) (nat_lit 0) D2M8K2.t7361 from rfl, totK_node, tot7360, tot7361]
  decide +kernel

theorem arows7356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7356 = true := by
  rw [show D2M8K2.u7356 = KTree.node D2M8K2.t7362 (nat_lit 15529541) (nat_lit 2290430254) (nat_lit 0) D2M8K2.t7363 from rfl, allE_node, rows7362, irow7356, rows7363]
  all_goals rfl

theorem atot7356 : totK PD2M8K2 D2M8K2.u7356 = [0, 160390059804, 701478775237, 774720744985, 163985066969, 2304167554, 0, 0] := by
  rw [show D2M8K2.u7356 = KTree.node D2M8K2.t7362 (nat_lit 15529541) (nat_lit 2290430254) (nat_lit 0) D2M8K2.t7363 from rfl, totK_node, tot7362, tot7363]
  decide +kernel

theorem arows7358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7358 = true := by
  rw [show D2M8K2.u7358 = KTree.node D2M8K2.t7364 (nat_lit 15531268) (nat_lit 3793132651) (nat_lit 0) D2M8K2.t7365 from rfl, allE_node, rows7364, irow7358, rows7365]
  all_goals rfl

theorem atot7358 : totK PD2M8K2 D2M8K2.u7358 = [0, 0, 365979958057, 935850838751, 444461001538, 28066945951, 0, 0] := by
  rw [show D2M8K2.u7358 = KTree.node D2M8K2.t7364 (nat_lit 15531268) (nat_lit 3793132651) (nat_lit 0) D2M8K2.t7365 from rfl, totK_node, tot7364, tot7365]
  decide +kernel

theorem arows7359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7359 = true := by
  rw [show D2M8K2.u7359 = KTree.node D2M8K2.t7366 (nat_lit 15535110) (nat_lit 3718457163) (nat_lit 0) D2M8K2.t7367 from rfl, allE_node, rows7366, irow7359, rows7367]
  all_goals rfl

theorem atot7359 : totK PD2M8K2 D2M8K2.u7359 = [0, 0, 370592040242, 926401967929, 481075141277, 41859531136, 0, 0] := by
  rw [show D2M8K2.u7359 = KTree.node D2M8K2.t7366 (nat_lit 15535110) (nat_lit 3718457163) (nat_lit 0) D2M8K2.t7367 from rfl, totK_node, tot7366, tot7367]
  decide +kernel

theorem arows7362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7362 = true := by
  rw [show D2M8K2.u7362 = KTree.node D2M8K2.t7368 (nat_lit 15536338) (nat_lit 4069434322) (nat_lit 0) D2M8K2.t7369 from rfl, allE_node, rows7368, irow7362, rows7369]
  all_goals rfl

theorem atot7362 : totK PD2M8K2 D2M8K2.u7362 = [0, 0, 364411461198, 951788836338, 467386504451, 30284591679, 0, 0] := by
  rw [show D2M8K2.u7362 = KTree.node D2M8K2.t7368 (nat_lit 15536338) (nat_lit 4069434322) (nat_lit 0) D2M8K2.t7369 from rfl, totK_node, tot7368, tot7369]
  decide +kernel

theorem arows7363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7363 = true := by
  rw [show D2M8K2.u7363 = KTree.node D2M8K2.t7370 (nat_lit 15539568) (nat_lit 3349834686) (nat_lit 0) D2M8K2.t7371 from rfl, allE_node, rows7370, irow7363, rows7371]
  all_goals rfl

theorem atot7363 : totK PD2M8K2 D2M8K2.u7363 = [0, 0, 267865622083, 822266204980, 603014313915, 91828506115, 1162935789, 0] := by
  rw [show D2M8K2.u7363 = KTree.node D2M8K2.t7370 (nat_lit 15539568) (nat_lit 3349834686) (nat_lit 0) D2M8K2.t7371 from rfl, totK_node, tot7370, tot7371]
  decide +kernel

theorem arows7365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7365 = true := by
  rw [show D2M8K2.u7365 = KTree.node D2M8K2.t7372 (nat_lit 15541256) (nat_lit 3643950755) (nat_lit 0) D2M8K2.t7373 from rfl, allE_node, rows7372, irow7365, rows7373]
  all_goals rfl

theorem atot7365 : totK PD2M8K2 D2M8K2.u7365 = [0, 0, 165297632584, 658885465160, 712779488106, 204661233459, 11853261585, 0] := by
  rw [show D2M8K2.u7365 = KTree.node D2M8K2.t7372 (nat_lit 15541256) (nat_lit 3643950755) (nat_lit 0) D2M8K2.t7373 from rfl, totK_node, tot7372, tot7373]
  decide +kernel

theorem arows7366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7366 = true := by
  rw [show D2M8K2.u7366 = KTree.node D2M8K2.t7374 (nat_lit 15546200) (nat_lit 3884234293) (nat_lit 0) D2M8K2.t7375 from rfl, allE_node, rows7374, irow7366, rows7375]
  all_goals rfl

theorem atot7366 : totK PD2M8K2 D2M8K2.u7366 = [0, 0, 245339661866, 842958126742, 603143079406, 76392340251, 1021600638, 0] := by
  rw [show D2M8K2.u7366 = KTree.node D2M8K2.t7374 (nat_lit 15546200) (nat_lit 3884234293) (nat_lit 0) D2M8K2.t7375 from rfl, totK_node, tot7374, tot7375]
  decide +kernel

theorem arows7370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7370 = true := by
  rw [show D2M8K2.u7370 = KTree.node D2M8K2.t7376 (nat_lit 15548626) (nat_lit 3882730019) (nat_lit 0) D2M8K2.t7377 from rfl, allE_node, rows7376, irow7370, rows7377]
  all_goals rfl

theorem atot7370 : totK PD2M8K2 D2M8K2.u7370 = [0, 0, 237134144079, 769732993768, 648051988941, 114244391734, 3552795014, 0] := by
  rw [show D2M8K2.u7370 = KTree.node D2M8K2.t7376 (nat_lit 15548626) (nat_lit 3882730019) (nat_lit 0) D2M8K2.t7377 from rfl, totK_node, tot7376, tot7377]
  decide +kernel

theorem arows7371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7371 = true := by
  rw [show D2M8K2.u7371 = KTree.node D2M8K2.t7378 (nat_lit 15550162) (nat_lit 4072409954) (nat_lit 0) D2M8K2.t7379 from rfl, allE_node, rows7378, irow7371, rows7379]
  all_goals rfl

theorem atot7371 : totK PD2M8K2 D2M8K2.u7371 = [0, 166746023996, 560146784264, 747310148650, 336556219460, 21894862632, 0, 0] := by
  rw [show D2M8K2.u7371 = KTree.node D2M8K2.t7378 (nat_lit 15550162) (nat_lit 4072409954) (nat_lit 0) D2M8K2.t7379 from rfl, totK_node, tot7378, tot7379]
  decide +kernel

theorem arows7373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7373 = true := by
  rw [show D2M8K2.u7373 = KTree.node D2M8K2.t7380 (nat_lit 15556832) (nat_lit 3776120356) (nat_lit 0) D2M8K2.t7381 from rfl, allE_node, rows7380, irow7373, rows7381]
  all_goals rfl

theorem atot7373 : totK PD2M8K2 D2M8K2.u7373 = [0, 262816873604, 814259599436, 611382896907, 122880775493, 13132762340, 0, 0] := by
  rw [show D2M8K2.u7373 = KTree.node D2M8K2.t7380 (nat_lit 15556832) (nat_lit 3776120356) (nat_lit 0) D2M8K2.t7381 from rfl, totK_node, tot7380, tot7381]
  decide +kernel

theorem arows7374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7374 = true := by
  rw [show D2M8K2.u7374 = KTree.node D2M8K2.t7382 (nat_lit 15558342) (nat_lit 3578879361) (nat_lit 0) D2M8K2.t7383 from rfl, allE_node, rows7382, irow7374, rows7383]
  all_goals rfl

theorem atot7374 : totK PD2M8K2 D2M8K2.u7374 = [0, 36575289639, 387189730187, 892278057461, 455658095782, 24462327659, 0, 0] := by
  rw [show D2M8K2.u7374 = KTree.node D2M8K2.t7382 (nat_lit 15558342) (nat_lit 3578879361) (nat_lit 0) D2M8K2.t7383 from rfl, totK_node, tot7382, tot7383]
  decide +kernel

theorem arows7377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7377 = true := by
  rw [show D2M8K2.u7377 = KTree.node D2M8K2.t7384 (nat_lit 15563342) (nat_lit 3794609127) (nat_lit 0) D2M8K2.t7385 from rfl, allE_node, rows7384, irow7377, rows7385]
  all_goals rfl

theorem atot7377 : totK PD2M8K2 D2M8K2.u7377 = [0, 390292462438, 936874410157, 468171777359, 35702429272, 0, 0, 0] := by
  rw [show D2M8K2.u7377 = KTree.node D2M8K2.t7384 (nat_lit 15563342) (nat_lit 3794609127) (nat_lit 0) D2M8K2.t7385 from rfl, totK_node, tot7384, tot7385]
  decide +kernel

theorem arows7378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7378 = true := by
  rw [show D2M8K2.u7378 = KTree.node D2M8K2.t7386 (nat_lit 15565033) (nat_lit 1490688371) (nat_lit 0) D2M8K2.t7387 from rfl, allE_node, rows7386, irow7378, rows7387]
  all_goals rfl

theorem atot7378 : totK PD2M8K2 D2M8K2.u7378 = [0, 0, 505884301410, 958326091352, 297323000591, 13250685261, 0, 0] := by
  rw [show D2M8K2.u7378 = KTree.node D2M8K2.t7386 (nat_lit 15565033) (nat_lit 1490688371) (nat_lit 0) D2M8K2.t7387 from rfl, totK_node, tot7386, tot7387]
  decide +kernel

theorem arows7380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7380 = true := by
  rw [show D2M8K2.u7380 = KTree.node D2M8K2.t7388 (nat_lit 15566420) (nat_lit 3232123941) (nat_lit 0) D2M8K2.t7389 from rfl, allE_node, rows7388, irow7380, rows7389]
  all_goals rfl

theorem atot7380 : totK PD2M8K2 D2M8K2.u7380 = [0, 369945481771, 895998853835, 496354215074, 51326594827, 0, 0, 0] := by
  rw [show D2M8K2.u7380 = KTree.node D2M8K2.t7388 (nat_lit 15566420) (nat_lit 3232123941) (nat_lit 0) D2M8K2.t7389 from rfl, totK_node, tot7388, tot7389]
  decide +kernel

theorem arows7381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7381 = true := by
  rw [show D2M8K2.u7381 = KTree.node D2M8K2.t7390 (nat_lit 15568428) (nat_lit 3432462437) (nat_lit 0) D2M8K2.t7391 from rfl, allE_node, rows7390, irow7381, rows7391]
  all_goals rfl

theorem atot7381 : totK PD2M8K2 D2M8K2.u7381 = [0, 98176748109, 694111289759, 840747435284, 162211413535, 3884009855, 0, 0] := by
  rw [show D2M8K2.u7381 = KTree.node D2M8K2.t7390 (nat_lit 15568428) (nat_lit 3432462437) (nat_lit 0) D2M8K2.t7391 from rfl, totK_node, tot7390, tot7391]
  decide +kernel

theorem arows7386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7386 = true := by
  rw [show D2M8K2.u7386 = KTree.node D2M8K2.t7392 (nat_lit 15570172) (nat_lit 3213233099) (nat_lit 0) D2M8K2.t7393 from rfl, allE_node, rows7392, irow7386, rows7393]
  all_goals rfl

theorem atot7386 : totK PD2M8K2 D2M8K2.u7386 = [0, 337788462646, 902822005593, 544738311187, 50876033005, 0, 0, 0] := by
  rw [show D2M8K2.u7386 = KTree.node D2M8K2.t7392 (nat_lit 15570172) (nat_lit 3213233099) (nat_lit 0) D2M8K2.t7393 from rfl, totK_node, tot7392, tot7393]
  decide +kernel

theorem arows7387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7387 = true := by
  rw [show D2M8K2.u7387 = KTree.node D2M8K2.t7394 (nat_lit 15571910) (nat_lit 4113510403) (nat_lit 0) D2M8K2.t7395 from rfl, allE_node, rows7394, irow7387, rows7395]
  all_goals rfl

theorem atot7387 : totK PD2M8K2 D2M8K2.u7387 = [0, 0, 424261313408, 962521720916, 382940094832, 18302234057, 0, 0] := by
  rw [show D2M8K2.u7387 = KTree.node D2M8K2.t7394 (nat_lit 15571910) (nat_lit 4113510403) (nat_lit 0) D2M8K2.t7395 from rfl, totK_node, tot7394, tot7395]
  decide +kernel

theorem arows7389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7389 = true := by
  rw [show D2M8K2.u7389 = KTree.node D2M8K2.t7396 (nat_lit 15577154) (nat_lit 4040595924) (nat_lit 0) D2M8K2.t7397 from rfl, allE_node, rows7396, irow7389, rows7397]
  all_goals rfl

theorem atot7389 : totK PD2M8K2 D2M8K2.u7389 = [0, 0, 390259681389, 943970829264, 469563764016, 35486171512, 0, 0] := by
  rw [show D2M8K2.u7389 = KTree.node D2M8K2.t7396 (nat_lit 15577154) (nat_lit 4040595924) (nat_lit 0) D2M8K2.t7397 from rfl, totK_node, tot7396, tot7397]
  decide +kernel

theorem arows7390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7390 = true := by
  rw [show D2M8K2.u7390 = KTree.node D2M8K2.t7398 (nat_lit 15583615) (nat_lit 2420449048) (nat_lit 0) D2M8K2.t7399 from rfl, allE_node, rows7398, irow7390, rows7399]
  all_goals rfl

theorem atot7390 : totK PD2M8K2 D2M8K2.u7390 = [0, 0, 338579423514, 913104754652, 516605223836, 39523479992, 0, 0] := by
  rw [show D2M8K2.u7390 = KTree.node D2M8K2.t7398 (nat_lit 15583615) (nat_lit 2420449048) (nat_lit 0) D2M8K2.t7399 from rfl, totK_node, tot7398, tot7399]
  decide +kernel

theorem arows7393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7393 = true := by
  rw [show D2M8K2.u7393 = KTree.node D2M8K2.t7400 (nat_lit 15585702) (nat_lit 3877539324) (nat_lit 0) D2M8K2.t7401 from rfl, allE_node, rows7400, irow7393, rows7401]
  all_goals rfl

theorem atot7393 : totK PD2M8K2 D2M8K2.u7393 = [0, 0, 87012357285, 656019263033, 832035936714, 188350173619, 5757108999, 0] := by
  rw [show D2M8K2.u7393 = KTree.node D2M8K2.t7400 (nat_lit 15585702) (nat_lit 3877539324) (nat_lit 0) D2M8K2.t7401 from rfl, totK_node, tot7400, tot7401]
  decide +kernel

theorem arows7394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7394 = true := by
  rw [show D2M8K2.u7394 = KTree.node D2M8K2.t7402 (nat_lit 15587184) (nat_lit 3262366744) (nat_lit 0) D2M8K2.t7403 from rfl, allE_node, rows7402, irow7394, rows7403]
  all_goals rfl

theorem atot7394 : totK PD2M8K2 D2M8K2.u7394 = [0, 0, 399128007315, 940513774834, 436639304755, 30704447637, 0, 0] := by
  rw [show D2M8K2.u7394 = KTree.node D2M8K2.t7402 (nat_lit 15587184) (nat_lit 3262366744) (nat_lit 0) D2M8K2.t7403 from rfl, totK_node, tot7402, tot7403]
  decide +kernel

theorem arows7396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7396 = true := by
  rw [show D2M8K2.u7396 = KTree.node D2M8K2.t7404 (nat_lit 15589279) (nat_lit 2357151223) (nat_lit 0) D2M8K2.t7405 from rfl, allE_node, rows7404, irow7396, rows7405]
  all_goals rfl

theorem atot7396 : totK PD2M8K2 D2M8K2.u7396 = [0, 0, 137659150004, 755758842536, 759455171676, 105571579117, 1376099875, 0] := by
  rw [show D2M8K2.u7396 = KTree.node D2M8K2.t7404 (nat_lit 15589279) (nat_lit 2357151223) (nat_lit 0) D2M8K2.t7405 from rfl, totK_node, tot7404, tot7405]
  decide +kernel

theorem arows7397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7397 = true := by
  rw [show D2M8K2.u7397 = KTree.node D2M8K2.t7406 (nat_lit 15591037) (nat_lit 1183270411) (nat_lit 0) D2M8K2.t7407 from rfl, allE_node, rows7406, irow7397, rows7407]
  all_goals rfl

theorem atot7397 : totK PD2M8K2 D2M8K2.u7397 = [0, 85146215446, 415171840927, 786687193554, 485091287538, 44031903765, 0, 0] := by
  rw [show D2M8K2.u7397 = KTree.node D2M8K2.t7406 (nat_lit 15591037) (nat_lit 1183270411) (nat_lit 0) D2M8K2.t7407 from rfl, totK_node, tot7406, tot7407]
  decide +kernel

theorem arows7401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7401 = true := by
  rw [show D2M8K2.u7401 = KTree.node D2M8K2.t7408 (nat_lit 15594642) (nat_lit 3362829394) (nat_lit 0) D2M8K2.t7409 from rfl, allE_node, rows7408, irow7401, rows7409]
  all_goals rfl

theorem atot7401 : totK PD2M8K2 D2M8K2.u7401 = [0, 238430358171, 820869098483, 622348853598, 93115590498, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7401 = KTree.node D2M8K2.t7408 (nat_lit 15594642) (nat_lit 3362829394) (nat_lit 0) D2M8K2.t7409 from rfl, totK_node, tot7408, tot7409]
  decide +kernel

theorem arows7402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7402 = true := by
  rw [show D2M8K2.u7402 = KTree.node D2M8K2.t7410 (nat_lit 15597459) (nat_lit 3700694319) (nat_lit 0) D2M8K2.t7411 from rfl, allE_node, rows7410, irow7402, rows7411]
  all_goals rfl

theorem atot7402 : totK PD2M8K2 D2M8K2.u7402 = [0, 266509405747, 836300319115, 653524373618, 70482840532, 0, 0, 0] := by
  rw [show D2M8K2.u7402 = KTree.node D2M8K2.t7410 (nat_lit 15597459) (nat_lit 3700694319) (nat_lit 0) D2M8K2.t7411 from rfl, totK_node, tot7410, tot7411]
  decide +kernel

theorem arows7404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7404 = true := by
  rw [show D2M8K2.u7404 = KTree.node D2M8K2.t7412 (nat_lit 15598991) (nat_lit 2136723247) (nat_lit 0) D2M8K2.t7413 from rfl, allE_node, rows7412, irow7404, rows7413]
  all_goals rfl

theorem atot7404 : totK PD2M8K2 D2M8K2.u7404 = [0, 162055487967, 630698573498, 717808482480, 280265671215, 25370006417, 0, 0] := by
  rw [show D2M8K2.u7404 = KTree.node D2M8K2.t7412 (nat_lit 15598991) (nat_lit 2136723247) (nat_lit 0) D2M8K2.t7413 from rfl, totK_node, tot7412, tot7413]
  decide +kernel

theorem arows7405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7405 = true := by
  rw [show D2M8K2.u7405 = KTree.node D2M8K2.t7414 (nat_lit 15600181) (nat_lit 599828076) (nat_lit 0) D2M8K2.t7415 from rfl, allE_node, rows7414, irow7405, rows7415]
  all_goals rfl

theorem atot7405 : totK PD2M8K2 D2M8K2.u7405 = [0, 166416896941, 588114310244, 737733912207, 303355139487, 12231701805, 0, 0] := by
  rw [show D2M8K2.u7405 = KTree.node D2M8K2.t7414 (nat_lit 15600181) (nat_lit 599828076) (nat_lit 0) D2M8K2.t7415 from rfl, totK_node, tot7414, tot7415]
  decide +kernel

theorem arows7408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7408 = true := by
  rw [show D2M8K2.u7408 = KTree.node D2M8K2.t7416 (nat_lit 15601692) (nat_lit 3071624997) (nat_lit 0) D2M8K2.t7417 from rfl, allE_node, rows7416, irow7408, rows7417]
  all_goals rfl

theorem atot7408 : totK PD2M8K2 D2M8K2.u7408 = [0, 249017254763, 797950642017, 651642485465, 102465538217, 1164319620, 0, 0] := by
  rw [show D2M8K2.u7408 = KTree.node D2M8K2.t7416 (nat_lit 15601692) (nat_lit 3071624997) (nat_lit 0) D2M8K2.t7417 from rfl, totK_node, tot7416, tot7417]
  decide +kernel

theorem arows7409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7409 = true := by
  rw [show D2M8K2.u7409 = KTree.node D2M8K2.t7418 (nat_lit 15603424) (nat_lit 2332861757) (nat_lit 0) D2M8K2.t7419 from rfl, allE_node, rows7418, irow7409, rows7419]
  all_goals rfl

theorem atot7409 : totK PD2M8K2 D2M8K2.u7409 = [0, 151752104418, 635593342982, 772661444218, 226826598784, 11885407614, 0, 0] := by
  rw [show D2M8K2.u7409 = KTree.node D2M8K2.t7418 (nat_lit 15603424) (nat_lit 2332861757) (nat_lit 0) D2M8K2.t7419 from rfl, totK_node, tot7418, tot7419]
  decide +kernel

theorem arows7411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7411 = true := by
  rw [show D2M8K2.u7411 = KTree.node D2M8K2.t7420 (nat_lit 15605142) (nat_lit 3581696511) (nat_lit 0) D2M8K2.t7421 from rfl, allE_node, rows7420, irow7411, rows7421]
  all_goals rfl

theorem atot7411 : totK PD2M8K2 D2M8K2.u7411 = [0, 231789590481, 828497546698, 667437979927, 74095726707, 0, 0, 0] := by
  rw [show D2M8K2.u7411 = KTree.node D2M8K2.t7420 (nat_lit 15605142) (nat_lit 3581696511) (nat_lit 0) D2M8K2.t7421 from rfl, totK_node, tot7420, tot7421]
  decide +kernel

theorem arows7412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7412 = true := by
  rw [show D2M8K2.u7412 = KTree.node D2M8K2.t7422 (nat_lit 15607128) (nat_lit 2912371984) (nat_lit 0) D2M8K2.t7423 from rfl, allE_node, rows7422, irow7412, rows7423]
  all_goals rfl

theorem atot7412 : totK PD2M8K2 D2M8K2.u7412 = [0, 170621121202, 650510256773, 740340418598, 222937941120, 12052611869, 0, 0] := by
  rw [show D2M8K2.u7412 = KTree.node D2M8K2.t7422 (nat_lit 15607128) (nat_lit 2912371984) (nat_lit 0) D2M8K2.t7423 from rfl, totK_node, tot7422, tot7423]
  decide +kernel

theorem arows7420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7420 = true := by
  rw [show D2M8K2.u7420 = KTree.node D2M8K2.t7424 (nat_lit 15608458) (nat_lit 2621448499) (nat_lit 0) D2M8K2.t7425 from rfl, allE_node, rows7424, irow7420, rows7425]
  all_goals rfl

theorem atot7420 : totK PD2M8K2 D2M8K2.u7420 = [0, 265686162196, 812621822652, 617185689966, 96297980179, 1096505104, 0, 0] := by
  rw [show D2M8K2.u7420 = KTree.node D2M8K2.t7424 (nat_lit 15608458) (nat_lit 2621448499) (nat_lit 0) D2M8K2.t7425 from rfl, totK_node, tot7424, tot7425]
  decide +kernel

theorem arows7421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7421 = true := by
  rw [show D2M8K2.u7421 = KTree.node D2M8K2.t7426 (nat_lit 15610393) (nat_lit 1302733211) (nat_lit 0) D2M8K2.t7427 from rfl, allE_node, rows7426, irow7421, rows7427]
  all_goals rfl

theorem atot7421 : totK PD2M8K2 D2M8K2.u7421 = [0, 0, 480935412121, 980661803874, 311512534617, 13624150839, 0, 0] := by
  rw [show D2M8K2.u7421 = KTree.node D2M8K2.t7426 (nat_lit 15610393) (nat_lit 1302733211) (nat_lit 0) D2M8K2.t7427 from rfl, totK_node, tot7426, tot7427]
  decide +kernel

theorem arows7423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7423 = true := by
  rw [show D2M8K2.u7423 = KTree.node D2M8K2.t7428 (nat_lit 15618064) (nat_lit 3382287894) (nat_lit 0) D2M8K2.t7429 from rfl, allE_node, rows7428, irow7423, rows7429]
  all_goals rfl

theorem atot7423 : totK PD2M8K2 D2M8K2.u7423 = [0, 0, 386849080963, 932583849003, 455069498247, 36819606270, 0, 0] := by
  rw [show D2M8K2.u7423 = KTree.node D2M8K2.t7428 (nat_lit 15618064) (nat_lit 3382287894) (nat_lit 0) D2M8K2.t7429 from rfl, totK_node, tot7428, tot7429]
  decide +kernel

theorem arows7424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7424 = true := by
  rw [show D2M8K2.u7424 = KTree.node D2M8K2.t7430 (nat_lit 15619304) (nat_lit 2712374115) (nat_lit 0) D2M8K2.t7431 from rfl, allE_node, rows7430, irow7424, rows7431]
  all_goals rfl

theorem atot7424 : totK PD2M8K2 D2M8K2.u7424 = [0, 0, 344644991936, 951856956277, 474577446380, 27757796708, 0, 0] := by
  rw [show D2M8K2.u7424 = KTree.node D2M8K2.t7430 (nat_lit 15619304) (nat_lit 2712374115) (nat_lit 0) D2M8K2.t7431 from rfl, totK_node, tot7430, tot7431]
  decide +kernel

theorem arows7427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7427 = true := by
  rw [show D2M8K2.u7427 = KTree.node D2M8K2.t7432 (nat_lit 15622571) (nat_lit 2542782370) (nat_lit 128) D2M8K2.t7433 from rfl, allE_node, rows7432, irow7427, rows7433]
  all_goals rfl

theorem atot7427 : totK PD2M8K2 D2M8K2.u7427 = [0, 0, 400211051695, 971551687753, 416847911694, 21773379448, 0, 0] := by
  rw [show D2M8K2.u7427 = KTree.node D2M8K2.t7432 (nat_lit 15622571) (nat_lit 2542782370) (nat_lit 128) D2M8K2.t7433 from rfl, totK_node, tot7432, tot7433]
  decide +kernel

theorem arows7428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7428 = true := by
  rw [show D2M8K2.u7428 = KTree.node D2M8K2.t7434 (nat_lit 15625921) (nat_lit 1292041965) (nat_lit 0) D2M8K2.t7435 from rfl, allE_node, rows7434, irow7428, rows7435]
  all_goals rfl

theorem atot7428 : totK PD2M8K2 D2M8K2.u7428 = [0, 0, 378732438654, 947560143371, 443557012621, 19377583332, 0, 0] := by
  rw [show D2M8K2.u7428 = KTree.node D2M8K2.t7434 (nat_lit 15625921) (nat_lit 1292041965) (nat_lit 0) D2M8K2.t7435 from rfl, totK_node, tot7434, tot7435]
  decide +kernel

theorem arows7430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7430 = true := by
  rw [show D2M8K2.u7430 = KTree.node D2M8K2.t7436 (nat_lit 15629004) (nat_lit 3138561861) (nat_lit 0) D2M8K2.t7437 from rfl, allE_node, rows7436, irow7430, rows7437]
  all_goals rfl

theorem atot7430 : totK PD2M8K2 D2M8K2.u7430 = [0, 0, 284138574407, 883217116469, 554258474542, 50301933165, 0, 0] := by
  rw [show D2M8K2.u7430 = KTree.node D2M8K2.t7436 (nat_lit 15629004) (nat_lit 3138561861) (nat_lit 0) D2M8K2.t7437 from rfl, totK_node, tot7436, tot7437]
  decide +kernel

theorem arows7431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7431 = true := by
  rw [show D2M8K2.u7431 = KTree.node D2M8K2.t7438 (nat_lit 15630976) (nat_lit 3558570782) (nat_lit 0) D2M8K2.t7439 from rfl, allE_node, rows7438, irow7431, rows7439]
  all_goals rfl

theorem atot7431 : totK PD2M8K2 D2M8K2.u7431 = [0, 169606407816, 349315023727, 446080751556, 617785445296, 170049305063, 4977114383, 0] := by
  rw [show D2M8K2.u7431 = KTree.node D2M8K2.t7438 (nat_lit 15630976) (nat_lit 3558570782) (nat_lit 0) D2M8K2.t7439 from rfl, totK_node, tot7438, tot7439]
  decide +kernel

theorem arows7435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7435 = true := by
  rw [show D2M8K2.u7435 = KTree.node D2M8K2.t7440 (nat_lit 15636619) (nat_lit 1585110918) (nat_lit 0) D2M8K2.t7441 from rfl, allE_node, rows7440, irow7435, rows7441]
  all_goals rfl

theorem atot7435 : totK PD2M8K2 D2M8K2.u7435 = [0, 157218413465, 749689859974, 783606000835, 122395283461, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7435 = KTree.node D2M8K2.t7440 (nat_lit 15636619) (nat_lit 1585110918) (nat_lit 0) D2M8K2.t7441 from rfl, totK_node, tot7440, tot7441]
  decide +kernel

theorem arows7436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7436 = true := by
  rw [show D2M8K2.u7436 = KTree.node D2M8K2.t7442 (nat_lit 15639108) (nat_lit 3052164971) (nat_lit 0) D2M8K2.t7443 from rfl, allE_node, rows7442, irow7436, rows7443]
  all_goals rfl

theorem atot7436 : totK PD2M8K2 D2M8K2.u7436 = [0, 339079349956, 889717647006, 546105145105, 55193893612, 0, 0, 0] := by
  rw [show D2M8K2.u7436 = KTree.node D2M8K2.t7442 (nat_lit 15639108) (nat_lit 3052164971) (nat_lit 0) D2M8K2.t7443 from rfl, totK_node, tot7442, tot7443]
  decide +kernel

theorem arows7438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7438 = true := by
  rw [show D2M8K2.u7438 = KTree.node D2M8K2.t7444 (nat_lit 15640629) (nat_lit 1046949771) (nat_lit 0) D2M8K2.t7445 from rfl, allE_node, rows7444, irow7438, rows7445]
  all_goals rfl

theorem atot7438 : totK PD2M8K2 D2M8K2.u7438 = [0, 90286224711, 536924180639, 822112151647, 343025228649, 28233755793, 0, 0] := by
  rw [show D2M8K2.u7438 = KTree.node D2M8K2.t7444 (nat_lit 15640629) (nat_lit 1046949771) (nat_lit 0) D2M8K2.t7445 from rfl, totK_node, tot7444, tot7445]
  decide +kernel

theorem arows7439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7439 = true := by
  rw [show D2M8K2.u7439 = KTree.node D2M8K2.t7446 (nat_lit 15641914) (nat_lit 3899492587) (nat_lit 0) D2M8K2.t7447 from rfl, allE_node, rows7446, irow7439, rows7447]
  all_goals rfl

theorem atot7439 : totK PD2M8K2 D2M8K2.u7439 = [0, 218981852525, 658222626454, 693792740670, 244724442879, 9355690997, 0, 0] := by
  rw [show D2M8K2.u7439 = KTree.node D2M8K2.t7446 (nat_lit 15641914) (nat_lit 3899492587) (nat_lit 0) D2M8K2.t7447 from rfl, totK_node, tot7446, tot7447]
  decide +kernel

theorem arows7442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7442 = true := by
  rw [show D2M8K2.u7442 = KTree.node D2M8K2.t7448 (nat_lit 15643440) (nat_lit 3678606079) (nat_lit 0) D2M8K2.t7449 from rfl, allE_node, rows7448, irow7442, rows7449]
  all_goals rfl

theorem atot7442 : totK PD2M8K2 D2M8K2.u7442 = [0, 193804049821, 777831083762, 721785320756, 118102540703, 1164319620, 0, 0] := by
  rw [show D2M8K2.u7442 = KTree.node D2M8K2.t7448 (nat_lit 15643440) (nat_lit 3678606079) (nat_lit 0) D2M8K2.t7449 from rfl, totK_node, tot7448, tot7449]
  decide +kernel

theorem arows7443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7443 = true := by
  rw [show D2M8K2.u7443 = KTree.node D2M8K2.t7450 (nat_lit 15645320) (nat_lit 2699169233) (nat_lit 0) D2M8K2.t7451 from rfl, allE_node, rows7450, irow7443, rows7451]
  all_goals rfl

theorem atot7443 : totK PD2M8K2 D2M8K2.u7443 = [0, 207781647148, 669295811194, 721533737793, 201787696717, 10871226512, 0, 0] := by
  rw [show D2M8K2.u7443 = KTree.node D2M8K2.t7450 (nat_lit 15645320) (nat_lit 2699169233) (nat_lit 0) D2M8K2.t7451 from rfl, totK_node, tot7450, tot7451]
  decide +kernel

theorem arows7445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7445 = true := by
  rw [show D2M8K2.u7445 = KTree.node D2M8K2.t7452 (nat_lit 15646954) (nat_lit 3984837731) (nat_lit 0) D2M8K2.t7453 from rfl, allE_node, rows7452, irow7445, rows7453]
  all_goals rfl

theorem atot7445 : totK PD2M8K2 D2M8K2.u7445 = [0, 177791839573, 764408293340, 749006593148, 123111775732, 1198073392, 0, 0] := by
  rw [show D2M8K2.u7445 = KTree.node D2M8K2.t7452 (nat_lit 15646954) (nat_lit 3984837731) (nat_lit 0) D2M8K2.t7453 from rfl, totK_node, tot7452, tot7453]
  decide +kernel

theorem arows7446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7446 = true := by
  rw [show D2M8K2.u7446 = KTree.node D2M8K2.t7454 (nat_lit 15652367) (nat_lit 2777085060) (nat_lit 0) D2M8K2.t7455 from rfl, allE_node, rows7454, irow7446, rows7455]
  all_goals rfl

theorem atot7446 : totK PD2M8K2 D2M8K2.u7446 = [0, 260574280212, 736156545586, 631824051620, 181511414453, 8401861322, 0, 0] := by
  rw [show D2M8K2.u7446 = KTree.node D2M8K2.t7454 (nat_lit 15652367) (nat_lit 2777085060) (nat_lit 0) D2M8K2.t7455 from rfl, totK_node, tot7454, tot7455]
  decide +kernel

theorem arows7451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7451 = true := by
  rw [show D2M8K2.u7451 = KTree.node D2M8K2.t7456 (nat_lit 15653834) (nat_lit 4212268741) (nat_lit 0) D2M8K2.t7457 from rfl, allE_node, rows7456, irow7451, rows7457]
  all_goals rfl

theorem atot7451 : totK PD2M8K2 D2M8K2.u7451 = [0, 180187839875, 747400413910, 749065328076, 134870161325, 1268739303, 0, 0] := by
  rw [show D2M8K2.u7451 = KTree.node D2M8K2.t7456 (nat_lit 15653834) (nat_lit 4212268741) (nat_lit 0) D2M8K2.t7457 from rfl, totK_node, tot7456, tot7457]
  decide +kernel

theorem arows7452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7452 = true := by
  rw [show D2M8K2.u7452 = KTree.node D2M8K2.t7458 (nat_lit 15655486) (nat_lit 3913318184) (nat_lit 0) D2M8K2.t7459 from rfl, allE_node, rows7458, irow7452, rows7459]
  all_goals rfl

theorem atot7452 : totK PD2M8K2 D2M8K2.u7452 = [0, 0, 391995736918, 954408535940, 400632545064, 22149860293, 0, 0] := by
  rw [show D2M8K2.u7452 = KTree.node D2M8K2.t7458 (nat_lit 15655486) (nat_lit 3913318184) (nat_lit 0) D2M8K2.t7459 from rfl, totK_node, tot7458, tot7459]
  decide +kernel

theorem arows7454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7454 = true := by
  rw [show D2M8K2.u7454 = KTree.node D2M8K2.t7460 (nat_lit 15657389) (nat_lit 2128585718) (nat_lit 0) D2M8K2.t7461 from rfl, allE_node, rows7460, irow7454, rows7461]
  all_goals rfl

theorem atot7454 : totK PD2M8K2 D2M8K2.u7454 = [0, 0, 156622574833, 755438424213, 772873875851, 103083874328, 1310285577, 0] := by
  rw [show D2M8K2.u7454 = KTree.node D2M8K2.t7460 (nat_lit 15657389) (nat_lit 2128585718) (nat_lit 0) D2M8K2.t7461 from rfl, totK_node, tot7460, tot7461]
  decide +kernel

theorem arows7455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7455 = true := by
  rw [show D2M8K2.u7455 = KTree.node D2M8K2.t7462 (nat_lit 15659868) (nat_lit 2857344698) (nat_lit 0) D2M8K2.t7463 from rfl, allE_node, rows7462, irow7455, rows7463]
  all_goals rfl

theorem atot7455 : totK PD2M8K2 D2M8K2.u7455 = [0, 0, 337762692693, 907802757212, 534812907587, 46569428877, 0, 0] := by
  rw [show D2M8K2.u7455 = KTree.node D2M8K2.t7462 (nat_lit 15659868) (nat_lit 2857344698) (nat_lit 0) D2M8K2.t7463 from rfl, totK_node, tot7462, tot7463]
  decide +kernel

theorem arows7458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7458 = true := by
  rw [show D2M8K2.u7458 = KTree.node D2M8K2.t7464 (nat_lit 15662936) (nat_lit 3649515165) (nat_lit 0) D2M8K2.t7465 from rfl, allE_node, rows7464, irow7458, rows7465]
  all_goals rfl

theorem atot7458 : totK PD2M8K2 D2M8K2.u7458 = [0, 0, 365698254783, 915064211215, 503498773236, 43942433512, 0, 0] := by
  rw [show D2M8K2.u7458 = KTree.node D2M8K2.t7464 (nat_lit 15662936) (nat_lit 3649515165) (nat_lit 0) D2M8K2.t7465 from rfl, totK_node, tot7464, tot7465]
  decide +kernel

theorem arows7459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7459 = true := by
  rw [show D2M8K2.u7459 = KTree.node D2M8K2.t7466 (nat_lit 15664446) (nat_lit 3378797813) (nat_lit 0) D2M8K2.t7467 from rfl, allE_node, rows7466, irow7459, rows7467]
  all_goals rfl

theorem atot7459 : totK PD2M8K2 D2M8K2.u7459 = [0, 0, 135721379837, 692450230457, 771563539310, 160557948348, 4879840392, 0] := by
  rw [show D2M8K2.u7459 = KTree.node D2M8K2.t7466 (nat_lit 15664446) (nat_lit 3378797813) (nat_lit 0) D2M8K2.t7467 from rfl, totK_node, tot7466, tot7467]
  decide +kernel

theorem arows7461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7461 = true := by
  rw [show D2M8K2.u7461 = KTree.node D2M8K2.t7468 (nat_lit 15666571) (nat_lit 1744291362) (nat_lit 0) D2M8K2.t7469 from rfl, allE_node, rows7468, irow7461, rows7469]
  all_goals rfl

theorem atot7461 : totK PD2M8K2 D2M8K2.u7461 = [0, 0, 334568775677, 901540490159, 537919369323, 50836446652, 0, 0] := by
  rw [show D2M8K2.u7461 = KTree.node D2M8K2.t7468 (nat_lit 15666571) (nat_lit 1744291362) (nat_lit 0) D2M8K2.t7469 from rfl, totK_node, tot7468, tot7469]
  decide +kernel

theorem arows7462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7462 = true := by
  rw [show D2M8K2.u7462 = KTree.node D2M8K2.t7470 (nat_lit 15668785) (nat_lit 1460163297) (nat_lit 0) D2M8K2.t7471 from rfl, allE_node, rows7470, irow7462, rows7471]
  all_goals rfl

theorem atot7462 : totK PD2M8K2 D2M8K2.u7462 = [0, 0, 162811810003, 783932469896, 749561771349, 114337397984, 1444560764, 0] := by
  rw [show D2M8K2.u7462 = KTree.node D2M8K2.t7470 (nat_lit 15668785) (nat_lit 1460163297) (nat_lit 0) D2M8K2.t7471 from rfl, totK_node, tot7470, tot7471]
  decide +kernel

theorem arows7466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7466 = true := by
  rw [show D2M8K2.u7466 = KTree.node D2M8K2.t7472 (nat_lit 15673856) (nat_lit 3400237337) (nat_lit 0) D2M8K2.t7473 from rfl, allE_node, rows7472, irow7466, rows7473]
  all_goals rfl

theorem atot7466 : totK PD2M8K2 D2M8K2.u7466 = [0, 0, 326365264929, 905896466167, 552402350023, 45231681454, 0, 0] := by
  rw [show D2M8K2.u7466 = KTree.node D2M8K2.t7472 (nat_lit 15673856) (nat_lit 3400237337) (nat_lit 0) D2M8K2.t7473 from rfl, totK_node, tot7472, tot7473]
  decide +kernel

theorem arows7467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7467 = true := by
  rw [show D2M8K2.u7467 = KTree.node D2M8K2.t7474 (nat_lit 15675539) (nat_lit 2920618751) (nat_lit 0) D2M8K2.t7475 from rfl, allE_node, rows7474, irow7467, rows7475]
  all_goals rfl

theorem atot7467 : totK PD2M8K2 D2M8K2.u7467 = [0, 37283609705, 39621360432, 397083704789, 909177254966, 347334503018, 18014152641, 0] := by
  rw [show D2M8K2.u7467 = KTree.node D2M8K2.t7474 (nat_lit 15675539) (nat_lit 2920618751) (nat_lit 0) D2M8K2.t7475 from rfl, totK_node, tot7474, tot7475]
  decide +kernel

theorem arows7469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7469 = true := by
  rw [show D2M8K2.u7469 = KTree.node D2M8K2.t7476 (nat_lit 15926211) (nat_lit 2987974749) (nat_lit 0) D2M8K2.t7477 from rfl, allE_node, rows7476, irow7469, rows7477]
  all_goals rfl

theorem atot7469 : totK PD2M8K2 D2M8K2.u7469 = [0, 394013160355, 955291103380, 424885407018, 22386190152, 0, 0, 0] := by
  rw [show D2M8K2.u7469 = KTree.node D2M8K2.t7476 (nat_lit 15926211) (nat_lit 2987974749) (nat_lit 0) D2M8K2.t7477 from rfl, totK_node, tot7476, tot7477]
  decide +kernel

theorem arows7470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7470 = true := by
  rw [show D2M8K2.u7470 = KTree.node D2M8K2.t7478 (nat_lit 15927851) (nat_lit 2870494911) (nat_lit 0) D2M8K2.t7479 from rfl, allE_node, rows7478, irow7470, rows7479]
  all_goals rfl

theorem atot7470 : totK PD2M8K2 D2M8K2.u7470 = [0, 91892778063, 673877310629, 890576135282, 154676182179, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7470 = KTree.node D2M8K2.t7478 (nat_lit 15927851) (nat_lit 2870494911) (nat_lit 0) D2M8K2.t7479 from rfl, totK_node, tot7478, tot7479]
  decide +kernel

theorem arows7473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7473 = true := by
  rw [show D2M8K2.u7473 = KTree.node D2M8K2.t7480 (nat_lit 15932937) (nat_lit 1757933004) (nat_lit 0) D2M8K2.t7481 from rfl, allE_node, rows7480, irow7473, rows7481]
  all_goals rfl

theorem atot7473 : totK PD2M8K2 D2M8K2.u7473 = [0, 338436945319, 927554573469, 511418886187, 36535378011, 0, 0, 0] := by
  rw [show D2M8K2.u7473 = KTree.node D2M8K2.t7480 (nat_lit 15932937) (nat_lit 1757933004) (nat_lit 0) D2M8K2.t7481 from rfl, totK_node, tot7480, tot7481]
  decide +kernel

theorem arows7474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7474 = true := by
  rw [show D2M8K2.u7474 = KTree.node D2M8K2.t7482 (nat_lit 15934612) (nat_lit 3746584604) (nat_lit 0) D2M8K2.t7483 from rfl, allE_node, rows7482, irow7474, rows7483]
  all_goals rfl

theorem atot7474 : totK PD2M8K2 D2M8K2.u7474 = [0, 33264521362, 483988056315, 950684019004, 299095376857, 13049727234, 0, 0] := by
  rw [show D2M8K2.u7474 = KTree.node D2M8K2.t7482 (nat_lit 15934612) (nat_lit 3746584604) (nat_lit 0) D2M8K2.t7483 from rfl, totK_node, tot7482, tot7483]
  decide +kernel

theorem arows7476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7476 = true := by
  rw [show D2M8K2.u7476 = KTree.node D2M8K2.t7484 (nat_lit 15936932) (nat_lit 3107572811) (nat_lit 0) D2M8K2.t7485 from rfl, allE_node, rows7484, irow7476, rows7485]
  all_goals rfl

theorem atot7476 : totK PD2M8K2 D2M8K2.u7476 = [0, 288594555472, 858337084955, 550220792052, 73003110079, 1198073392, 0, 0] := by
  rw [show D2M8K2.u7476 = KTree.node D2M8K2.t7484 (nat_lit 15936932) (nat_lit 3107572811) (nat_lit 0) D2M8K2.t7485 from rfl, totK_node, tot7484, tot7485]
  decide +kernel

theorem arows7477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7477 = true := by
  rw [show D2M8K2.u7477 = KTree.node D2M8K2.t7486 (nat_lit 15939142) (nat_lit 3431886663) (nat_lit 0) D2M8K2.t7487 from rfl, allE_node, rows7486, irow7477, rows7487]
  all_goals rfl

theorem atot7477 : totK PD2M8K2 D2M8K2.u7477 = [0, 241865314003, 753776091797, 663802503594, 126650318682, 3581949829, 0, 0] := by
  rw [show D2M8K2.u7477 = KTree.node D2M8K2.t7486 (nat_lit 15939142) (nat_lit 3431886663) (nat_lit 0) D2M8K2.t7487 from rfl, totK_node, tot7486, tot7487]
  decide +kernel

theorem arows7483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7483 = true := by
  rw [show D2M8K2.u7483 = KTree.node D2M8K2.t7488 (nat_lit 15940390) (nat_lit 1185767456) (nat_lit 0) D2M8K2.t7489 from rfl, allE_node, rows7488, irow7483, rows7489]
  all_goals rfl

theorem atot7483 : totK PD2M8K2 D2M8K2.u7483 = [0, 166673409451, 756380947895, 736774909544, 108919884777, 1096505104, 0, 0] := by
  rw [show D2M8K2.u7483 = KTree.node D2M8K2.t7488 (nat_lit 15940390) (nat_lit 1185767456) (nat_lit 0) D2M8K2.t7489 from rfl, totK_node, tot7488, tot7489]
  decide +kernel

theorem arows7484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7484 = true := by
  rw [show D2M8K2.u7484 = KTree.node D2M8K2.t7490 (nat_lit 15942682) (nat_lit 3849923367) (nat_lit 0) D2M8K2.t7491 from rfl, allE_node, rows7490, irow7484, rows7491]
  all_goals rfl

theorem atot7484 : totK PD2M8K2 D2M8K2.u7484 = [0, 244324912864, 769157331941, 650962720470, 130466250236, 3884009855, 0, 0] := by
  rw [show D2M8K2.u7484 = KTree.node D2M8K2.t7490 (nat_lit 15942682) (nat_lit 3849923367) (nat_lit 0) D2M8K2.t7491 from rfl, totK_node, tot7490, tot7491]
  decide +kernel

theorem arows7486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7486 = true := by
  rw [show D2M8K2.u7486 = KTree.node D2M8K2.t7492 (nat_lit 15944245) (nat_lit 1310860937) (nat_lit 0) D2M8K2.t7493 from rfl, allE_node, rows7492, irow7486, rows7493]
  all_goals rfl

theorem atot7486 : totK PD2M8K2 D2M8K2.u7486 = [0, 169300515430, 699343028832, 761522953975, 163297327009, 2304167554, 0, 0] := by
  rw [show D2M8K2.u7486 = KTree.node D2M8K2.t7492 (nat_lit 15944245) (nat_lit 1310860937) (nat_lit 0) D2M8K2.t7493 from rfl, totK_node, tot7492, tot7493]
  decide +kernel

theorem arows7487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7487 = true := by
  rw [show D2M8K2.u7487 = KTree.node D2M8K2.t7494 (nat_lit 15945971) (nat_lit 2971816977) (nat_lit 0) D2M8K2.t7495 from rfl, allE_node, rows7494, irow7487, rows7495]
  all_goals rfl

theorem atot7487 : totK PD2M8K2 D2M8K2.u7487 = [0, 0, 365463498464, 947029436913, 427419149318, 24858797182, 0, 0] := by
  rw [show D2M8K2.u7487 = KTree.node D2M8K2.t7494 (nat_lit 15945971) (nat_lit 2971816977) (nat_lit 0) D2M8K2.t7495 from rfl, totK_node, tot7494, tot7495]
  decide +kernel

theorem arows7490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7490 = true := by
  rw [show D2M8K2.u7490 = KTree.node D2M8K2.t7496 (nat_lit 15947492) (nat_lit 2543924880) (nat_lit 0) D2M8K2.t7497 from rfl, allE_node, rows7496, irow7490, rows7497]
  all_goals rfl

theorem atot7490 : totK PD2M8K2 D2M8K2.u7490 = [0, 0, 236613916588, 793716446166, 599850790243, 95745411373, 1369150432, 0] := by
  rw [show D2M8K2.u7490 = KTree.node D2M8K2.t7496 (nat_lit 15947492) (nat_lit 2543924880) (nat_lit 0) D2M8K2.t7497 from rfl, totK_node, tot7496, tot7497]
  decide +kernel

theorem arows7491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7491 = true := by
  rw [show D2M8K2.u7491 = KTree.node D2M8K2.t7498 (nat_lit 15953050) (nat_lit 3804900506) (nat_lit 0) D2M8K2.t7499 from rfl, allE_node, rows7498, irow7491, rows7499]
  all_goals rfl

theorem atot7491 : totK PD2M8K2 D2M8K2.u7491 = [0, 0, 252424499711, 871435424748, 592098388271, 47846153521, 0, 0] := by
  rw [show D2M8K2.u7491 = KTree.node D2M8K2.t7498 (nat_lit 15953050) (nat_lit 3804900506) (nat_lit 0) D2M8K2.t7499 from rfl, totK_node, tot7498, tot7499]
  decide +kernel

theorem arows7493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7493 = true := by
  rw [show D2M8K2.u7493 = KTree.node D2M8K2.t7500 (nat_lit 15956360) (nat_lit 3604243563) (nat_lit 0) D2M8K2.t7501 from rfl, allE_node, rows7500, irow7493, rows7501]
  all_goals rfl

theorem atot7493 : totK PD2M8K2 D2M8K2.u7493 = [0, 0, 407112662589, 957510839674, 387050474813, 16586146683, 0, 0] := by
  rw [show D2M8K2.u7493 = KTree.node D2M8K2.t7500 (nat_lit 15956360) (nat_lit 3604243563) (nat_lit 0) D2M8K2.t7501 from rfl, totK_node, tot7500, tot7501]
  decide +kernel

theorem arows7494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7494 = true := by
  rw [show D2M8K2.u7494 = KTree.node D2M8K2.t7502 (nat_lit 15960025) (nat_lit 1497717970) (nat_lit 0) D2M8K2.t7503 from rfl, allE_node, rows7502, irow7494, rows7503]
  all_goals rfl

theorem atot7494 : totK PD2M8K2 D2M8K2.u7494 = [0, 0, 354401173405, 959453995940, 430112791707, 19256832118, 0, 0] := by
  rw [show D2M8K2.u7494 = KTree.node D2M8K2.t7502 (nat_lit 15960025) (nat_lit 1497717970) (nat_lit 0) D2M8K2.t7503 from rfl, totK_node, tot7502, tot7503]
  decide +kernel

theorem arows7498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7498 = true := by
  rw [show D2M8K2.u7498 = KTree.node D2M8K2.t7504 (nat_lit 15963373) (nat_lit 1133093022) (nat_lit 0) D2M8K2.t7505 from rfl, allE_node, rows7504, irow7498, rows7505]
  all_goals rfl

theorem atot7498 : totK PD2M8K2 D2M8K2.u7498 = [0, 0, 379702946667, 965832146991, 417206021677, 14429721991, 0, 0] := by
  rw [show D2M8K2.u7498 = KTree.node D2M8K2.t7504 (nat_lit 15963373) (nat_lit 1133093022) (nat_lit 0) D2M8K2.t7505 from rfl, totK_node, tot7504, tot7505]
  decide +kernel

theorem arows7499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7499 = true := by
  rw [show D2M8K2.u7499 = KTree.node D2M8K2.t7506 (nat_lit 15964986) (nat_lit 3369046935) (nat_lit 0) D2M8K2.t7507 from rfl, allE_node, rows7506, irow7499, rows7507]
  all_goals rfl

theorem atot7499 : totK PD2M8K2 D2M8K2.u7499 = [0, 183243395725, 622428857801, 729747037148, 278101277737, 15558391480, 0, 0] := by
  rw [show D2M8K2.u7499 = KTree.node D2M8K2.t7506 (nat_lit 15964986) (nat_lit 3369046935) (nat_lit 0) D2M8K2.t7507 from rfl, totK_node, tot7506, tot7507]
  decide +kernel

theorem arows7501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7501 = true := by
  rw [show D2M8K2.u7501 = KTree.node D2M8K2.t7508 (nat_lit 15971634) (nat_lit 3050701004) (nat_lit 0) D2M8K2.t7509 from rfl, allE_node, rows7508, irow7501, rows7509]
  all_goals rfl

theorem atot7501 : totK PD2M8K2 D2M8K2.u7501 = [0, 260842148793, 781521682830, 604381446495, 170290902076, 17186218589, 0, 0] := by
  rw [show D2M8K2.u7501 = KTree.node D2M8K2.t7508 (nat_lit 15971634) (nat_lit 3050701004) (nat_lit 0) D2M8K2.t7509 from rfl, totK_node, tot7508, tot7509]
  decide +kernel

theorem arows7502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7502 = true := by
  rw [show D2M8K2.u7502 = KTree.node D2M8K2.t7510 (nat_lit 15973091) (nat_lit 2323206573) (nat_lit 0) D2M8K2.t7511 from rfl, allE_node, rows7510, irow7502, rows7511]
  all_goals rfl

theorem atot7502 : totK PD2M8K2 D2M8K2.u7502 = [0, 53342041414, 430346989439, 889718403918, 412217764316, 20423179516, 0, 0] := by
  rw [show D2M8K2.u7502 = KTree.node D2M8K2.t7510 (nat_lit 15973091) (nat_lit 2323206573) (nat_lit 0) D2M8K2.t7511 from rfl, totK_node, tot7510, tot7511]
  decide +kernel

theorem arows7505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7505 = true := by
  rw [show D2M8K2.u7505 = KTree.node D2M8K2.t7512 (nat_lit 15974342) (nat_lit 3968173516) (nat_lit 0) D2M8K2.t7513 from rfl, allE_node, rows7512, irow7505, rows7513]
  all_goals rfl

theorem atot7505 : totK PD2M8K2 D2M8K2.u7505 = [0, 374039308549, 944734056575, 481206295816, 35734416333, 0, 0, 0] := by
  rw [show D2M8K2.u7505 = KTree.node D2M8K2.t7512 (nat_lit 15974342) (nat_lit 3968173516) (nat_lit 0) D2M8K2.t7513 from rfl, totK_node, tot7512, tot7513]
  decide +kernel

theorem arows7506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7506 = true := by
  rw [show D2M8K2.u7506 = KTree.node D2M8K2.t7514 (nat_lit 15976034) (nat_lit 3997378488) (nat_lit 0) D2M8K2.t7515 from rfl, allE_node, rows7514, irow7506, rows7515]
  all_goals rfl

theorem atot7506 : totK PD2M8K2 D2M8K2.u7506 = [0, 0, 494104204482, 981828895158, 295078498581, 13036865798, 0, 0] := by
  rw [show D2M8K2.u7506 = KTree.node D2M8K2.t7514 (nat_lit 15976034) (nat_lit 3997378488) (nat_lit 0) D2M8K2.t7515 from rfl, totK_node, tot7514, tot7515]
  decide +kernel

theorem arows7508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7508 = true := by
  rw [show D2M8K2.u7508 = KTree.node D2M8K2.t7516 (nat_lit 15978269) (nat_lit 2137722191) (nat_lit 0) D2M8K2.t7517 from rfl, allE_node, rows7516, irow7508, rows7517]
  all_goals rfl

theorem atot7508 : totK PD2M8K2 D2M8K2.u7508 = [0, 328796786280, 902326212945, 559451557155, 61444257264, 0, 0, 0] := by
  rw [show D2M8K2.u7508 = KTree.node D2M8K2.t7516 (nat_lit 15978269) (nat_lit 2137722191) (nat_lit 0) D2M8K2.t7517 from rfl, totK_node, tot7516, tot7517]
  decide +kernel

theorem arows7509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7509 = true := by
  rw [show D2M8K2.u7509 = KTree.node D2M8K2.t7518 (nat_lit 15980298) (nat_lit 3843874073) (nat_lit 0) D2M8K2.t7519 from rfl, allE_node, rows7518, irow7509, rows7519]
  all_goals rfl

theorem atot7509 : totK PD2M8K2 D2M8K2.u7509 = [0, 156219903603, 658497146545, 781605813465, 202139477865, 7024963918, 0, 0] := by
  rw [show D2M8K2.u7509 = KTree.node D2M8K2.t7518 (nat_lit 15980298) (nat_lit 3843874073) (nat_lit 0) D2M8K2.t7519 from rfl, totK_node, tot7518, tot7519]
  decide +kernel

theorem arows7514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7514 = true := by
  rw [show D2M8K2.u7514 = KTree.node D2M8K2.t7520 (nat_lit 15981706) (nat_lit 1935451892) (nat_lit 0) D2M8K2.t7521 from rfl, allE_node, rows7520, irow7514, rows7521]
  all_goals rfl

theorem atot7514 : totK PD2M8K2 D2M8K2.u7514 = [0, 255354297318, 812552378768, 636453695579, 92597326090, 1096156699, 0, 0] := by
  rw [show D2M8K2.u7514 = KTree.node D2M8K2.t7520 (nat_lit 15981706) (nat_lit 1935451892) (nat_lit 0) D2M8K2.t7521 from rfl, totK_node, tot7520, tot7521]
  decide +kernel

theorem arows7515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7515 = true := by
  rw [show D2M8K2.u7515 = KTree.node D2M8K2.t7522 (nat_lit 15984004) (nat_lit 3724415699) (nat_lit 0) D2M8K2.t7523 from rfl, allE_node, rows7522, irow7515, rows7523]
  all_goals rfl

theorem atot7515 : totK PD2M8K2 D2M8K2.u7515 = [0, 200918485339, 726713290721, 748218127438, 148899000896, 3880716147, 0, 0] := by
  rw [show D2M8K2.u7515 = KTree.node D2M8K2.t7522 (nat_lit 15984004) (nat_lit 3724415699) (nat_lit 0) D2M8K2.t7523 from rfl, totK_node, tot7522, tot7523]
  decide +kernel

theorem arows7517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7517 = true := by
  rw [show D2M8K2.u7517 = KTree.node D2M8K2.t7524 (nat_lit 15985525) (nat_lit 1184299121) (nat_lit 0) D2M8K2.t7525 from rfl, allE_node, rows7524, irow7517, rows7525]
  all_goals rfl

theorem atot7517 : totK PD2M8K2 D2M8K2.u7517 = [0, 216127886953, 786784911942, 696159133705, 115114491695, 1267860612, 0, 0] := by
  rw [show D2M8K2.u7517 = KTree.node D2M8K2.t7524 (nat_lit 15985525) (nat_lit 1184299121) (nat_lit 0) D2M8K2.t7525 from rfl, totK_node, tot7524, tot7525]
  decide +kernel

theorem arows7518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7518 = true := by
  rw [show D2M8K2.u7518 = KTree.node D2M8K2.t7526 (nat_lit 15987252) (nat_lit 2951573185) (nat_lit 0) D2M8K2.t7527 from rfl, allE_node, rows7526, irow7518, rows7527]
  all_goals rfl

theorem atot7518 : totK PD2M8K2 D2M8K2.u7518 = [0, 0, 368071501211, 915709880084, 480084137860, 41325803568, 0, 0] := by
  rw [show D2M8K2.u7518 = KTree.node D2M8K2.t7526 (nat_lit 15987252) (nat_lit 2951573185) (nat_lit 0) D2M8K2.t7527 from rfl, totK_node, tot7526, tot7527]
  decide +kernel

theorem arows7521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7521 = true := by
  rw [show D2M8K2.u7521 = KTree.node D2M8K2.t7528 (nat_lit 15992147) (nat_lit 2055682839) (nat_lit 0) D2M8K2.t7529 from rfl, allE_node, rows7528, irow7521, rows7529]
  all_goals rfl

theorem atot7521 : totK PD2M8K2 D2M8K2.u7521 = [0, 0, 304208532757, 911802444077, 564791096643, 46359542774, 0, 0] := by
  rw [show D2M8K2.u7521 = KTree.node D2M8K2.t7528 (nat_lit 15992147) (nat_lit 2055682839) (nat_lit 0) D2M8K2.t7529 from rfl, totK_node, tot7528, tot7529]
  decide +kernel

theorem arows7522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7522 = true := by
  rw [show D2M8K2.u7522 = KTree.node D2M8K2.t7530 (nat_lit 15993819) (nat_lit 3766489105) (nat_lit 0) D2M8K2.t7531 from rfl, allE_node, rows7530, irow7522, rows7531]
  all_goals rfl

theorem atot7522 : totK PD2M8K2 D2M8K2.u7522 = [0, 0, 66570406258, 445875750805, 861539795517, 390999571839, 24281722747, 0] := by
  rw [show D2M8K2.u7522 = KTree.node D2M8K2.t7530 (nat_lit 15993819) (nat_lit 3766489105) (nat_lit 0) D2M8K2.t7531 from rfl, totK_node, tot7530, tot7531]
  decide +kernel

theorem arows7524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7524 = true := by
  rw [show D2M8K2.u7524 = KTree.node D2M8K2.t7532 (nat_lit 15995092) (nat_lit 3772581810) (nat_lit 0) D2M8K2.t7533 from rfl, allE_node, rows7532, irow7524, rows7533]
  all_goals rfl

theorem atot7524 : totK PD2M8K2 D2M8K2.u7524 = [0, 0, 359179509747, 937465528886, 490058183173, 36199717542, 0, 0] := by
  rw [show D2M8K2.u7524 = KTree.node D2M8K2.t7532 (nat_lit 15995092) (nat_lit 3772581810) (nat_lit 0) D2M8K2.t7533 from rfl, totK_node, tot7532, tot7533]
  decide +kernel

theorem arows7525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7525 = true := by
  rw [show D2M8K2.u7525 = KTree.node D2M8K2.t7534 (nat_lit 15996912) (nat_lit 3074050851) (nat_lit 0) D2M8K2.t7535 from rfl, allE_node, rows7534, irow7525, rows7535]
  all_goals rfl

theorem atot7525 : totK PD2M8K2 D2M8K2.u7525 = [0, 0, 89631789061, 616745837039, 887070273014, 205162210149, 5159868635, 0] := by
  rw [show D2M8K2.u7525 = KTree.node D2M8K2.t7534 (nat_lit 15996912) (nat_lit 3074050851) (nat_lit 0) D2M8K2.t7535 from rfl, totK_node, tot7534, tot7535]
  decide +kernel

theorem arows7529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7529 = true := by
  rw [show D2M8K2.u7529 = KTree.node D2M8K2.t7536 (nat_lit 15999194) (nat_lit 3990833914) (nat_lit 0) D2M8K2.t7537 from rfl, allE_node, rows7536, irow7529, rows7537]
  all_goals rfl

theorem atot7529 : totK PD2M8K2 D2M8K2.u7529 = [0, 0, 342013240723, 910451963388, 514155689867, 40453845832, 0, 0] := by
  rw [show D2M8K2.u7529 = KTree.node D2M8K2.t7536 (nat_lit 15999194) (nat_lit 3990833914) (nat_lit 0) D2M8K2.t7537 from rfl, totK_node, tot7536, tot7537]
  decide +kernel

theorem arows7530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7530 = true := by
  rw [show D2M8K2.u7530 = KTree.node D2M8K2.t7538 (nat_lit 16002184) (nat_lit 3231841302) (nat_lit 0) D2M8K2.t7539 from rfl, allE_node, rows7538, irow7530, rows7539]
  all_goals rfl

theorem atot7530 : totK PD2M8K2 D2M8K2.u7530 = [0, 0, 306652434962, 897104879953, 549400799567, 42311508006, 0, 0] := by
  rw [show D2M8K2.u7530 = KTree.node D2M8K2.t7538 (nat_lit 16002184) (nat_lit 3231841302) (nat_lit 0) D2M8K2.t7539 from rfl, totK_node, tot7538, tot7539]
  decide +kernel

theorem arows7532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7532 = true := by
  rw [show D2M8K2.u7532 = KTree.node D2M8K2.t7540 (nat_lit 16004312) (nat_lit 3614762614) (nat_lit 0) D2M8K2.t7541 from rfl, allE_node, rows7540, irow7532, rows7541]
  all_goals rfl

theorem atot7532 : totK PD2M8K2 D2M8K2.u7532 = [0, 0, 157866674996, 744645327266, 798015389407, 131962407111, 1415142070, 0] := by
  rw [show D2M8K2.u7532 = KTree.node D2M8K2.t7540 (nat_lit 16004312) (nat_lit 3614762614) (nat_lit 0) D2M8K2.t7541 from rfl, totK_node, tot7540, tot7541]
  decide +kernel

theorem arows7533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7533 = true := by
  rw [show D2M8K2.u7533 = KTree.node D2M8K2.t7542 (nat_lit 16006209) (nat_lit 1272203910) (nat_lit 0) D2M8K2.t7543 from rfl, allE_node, rows7542, irow7533, rows7543]
  all_goals rfl

theorem atot7533 : totK PD2M8K2 D2M8K2.u7533 = [0, 0, 258091064876, 867712383674, 614927535384, 66550729934, 0, 0] := by
  rw [show D2M8K2.u7533 = KTree.node D2M8K2.t7542 (nat_lit 16006209) (nat_lit 1272203910) (nat_lit 0) D2M8K2.t7543 from rfl, totK_node, tot7542, tot7543]
  decide +kernel

theorem arows7536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7536 = true := by
  rw [show D2M8K2.u7536 = KTree.node D2M8K2.t7544 (nat_lit 16008249) (nat_lit 1822536073) (nat_lit 0) D2M8K2.t7545 from rfl, allE_node, rows7544, irow7536, rows7545]
  all_goals rfl

theorem atot7536 : totK PD2M8K2 D2M8K2.u7536 = [0, 227620798624, 525763270761, 405286505674, 459342362373, 167232334729, 5510671013, 0] := by
  rw [show D2M8K2.u7536 = KTree.node D2M8K2.t7544 (nat_lit 16008249) (nat_lit 1822536073) (nat_lit 0) D2M8K2.t7545 from rfl, totK_node, tot7544, tot7545]
  decide +kernel

theorem arows7537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7537 = true := by
  rw [show D2M8K2.u7537 = KTree.node D2M8K2.t7546 (nat_lit 16009788) (nat_lit 3260440895) (nat_lit 0) D2M8K2.t7547 from rfl, allE_node, rows7546, irow7537, rows7547]
  all_goals rfl

theorem atot7537 : totK PD2M8K2 D2M8K2.u7537 = [0, 189161375557, 744423998356, 720774677475, 118539061033, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7537 = KTree.node D2M8K2.t7546 (nat_lit 16009788) (nat_lit 3260440895) (nat_lit 0) D2M8K2.t7547 from rfl, totK_node, tot7546, tot7547]
  decide +kernel

theorem arows7539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7539 = true := by
  rw [show D2M8K2.u7539 = KTree.node D2M8K2.t7548 (nat_lit 16012139) (nat_lit 2729817035) (nat_lit 0) D2M8K2.t7549 from rfl, allE_node, rows7548, irow7539, rows7549]
  all_goals rfl

theorem atot7539 : totK PD2M8K2 D2M8K2.u7539 = [0, 252077940308, 833280400508, 677413001671, 74761729934, 0, 0, 0] := by
  rw [show D2M8K2.u7539 = KTree.node D2M8K2.t7548 (nat_lit 16012139) (nat_lit 2729817035) (nat_lit 0) D2M8K2.t7549 from rfl, totK_node, tot7548, tot7549]
  decide +kernel

theorem arows7540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7540 = true := by
  rw [show D2M8K2.u7540 = KTree.node D2M8K2.t7550 (nat_lit 16013371) (nat_lit 1491925155) (nat_lit 0) D2M8K2.t7551 from rfl, allE_node, rows7550, irow7540, rows7551]
  all_goals rfl

theorem atot7540 : totK PD2M8K2 D2M8K2.u7540 = [0, 174333546275, 647303404639, 701026970967, 271029224224, 24987864049, 0, 0] := by
  rw [show D2M8K2.u7540 = KTree.node D2M8K2.t7550 (nat_lit 16013371) (nat_lit 1491925155) (nat_lit 0) D2M8K2.t7551 from rfl, totK_node, tot7550, tot7551]
  decide +kernel

theorem arows7547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7547 = true := by
  rw [show D2M8K2.u7547 = KTree.node D2M8K2.t7552 (nat_lit 16014891) (nat_lit 3631582253) (nat_lit 0) D2M8K2.t7553 from rfl, allE_node, rows7552, irow7547, rows7553]
  all_goals rfl

theorem atot7547 : totK PD2M8K2 D2M8K2.u7547 = [0, 176559373540, 599243132595, 735994312440, 295179932857, 10154928807, 0, 0] := by
  rw [show D2M8K2.u7547 = KTree.node D2M8K2.t7552 (nat_lit 16014891) (nat_lit 3631582253) (nat_lit 0) D2M8K2.t7553 from rfl, totK_node, tot7552, tot7553]
  decide +kernel

theorem arows7548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7548 = true := by
  rw [show D2M8K2.u7548 = KTree.node D2M8K2.t7554 (nat_lit 16016353) (nat_lit 1487679972) (nat_lit 0) D2M8K2.t7555 from rfl, allE_node, rows7554, irow7548, rows7555]
  all_goals rfl

theorem atot7548 : totK PD2M8K2 D2M8K2.u7548 = [0, 270019299043, 872311504113, 631851513348, 60722633500, 0, 0, 0] := by
  rw [show D2M8K2.u7548 = KTree.node D2M8K2.t7554 (nat_lit 16016353) (nat_lit 1487679972) (nat_lit 0) D2M8K2.t7555 from rfl, totK_node, tot7554, tot7555]
  decide +kernel

theorem arows7550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7550 = true := by
  rw [show D2M8K2.u7550 = KTree.node D2M8K2.t7556 (nat_lit 16018024) (nat_lit 3761714959) (nat_lit 0) D2M8K2.t7557 from rfl, allE_node, rows7556, irow7550, rows7557]
  all_goals rfl

theorem atot7550 : totK PD2M8K2 D2M8K2.u7550 = [0, 84415941621, 541778260161, 870413053613, 279055054870, 13049727234, 0, 0] := by
  rw [show D2M8K2.u7550 = KTree.node D2M8K2.t7556 (nat_lit 16018024) (nat_lit 3761714959) (nat_lit 0) D2M8K2.t7557 from rfl, totK_node, tot7556, tot7557]
  decide +kernel

theorem arows7551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7551 = true := by
  rw [show D2M8K2.u7551 = KTree.node D2M8K2.t7558 (nat_lit 16022834) (nat_lit 3949341186) (nat_lit 0) D2M8K2.t7559 from rfl, allE_node, rows7558, irow7551, rows7559]
  all_goals rfl

theorem atot7551 : totK PD2M8K2 D2M8K2.u7551 = [0, 335068272917, 910857456414, 527352721718, 41921217836, 0, 0, 0] := by
  rw [show D2M8K2.u7551 = KTree.node D2M8K2.t7558 (nat_lit 16022834) (nat_lit 3949341186) (nat_lit 0) D2M8K2.t7559 from rfl, totK_node, tot7558, tot7559]
  decide +kernel

theorem arows7554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7554 = true := by
  rw [show D2M8K2.u7554 = KTree.node D2M8K2.t7560 (nat_lit 16024701) (nat_lit 1523337085) (nat_lit 0) D2M8K2.t7561 from rfl, allE_node, rows7560, irow7554, rows7561]
  all_goals rfl

theorem atot7554 : totK PD2M8K2 D2M8K2.u7554 = [0, 104743417926, 623142560774, 858802887085, 197623993611, 4980514959, 0, 0] := by
  rw [show D2M8K2.u7554 = KTree.node D2M8K2.t7560 (nat_lit 16024701) (nat_lit 1523337085) (nat_lit 0) D2M8K2.t7561 from rfl, totK_node, tot7560, tot7561]
  decide +kernel

theorem arows7555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7555 = true := by
  rw [show D2M8K2.u7555 = KTree.node D2M8K2.t7562 (nat_lit 16026347) (nat_lit 2902754041) (nat_lit 0) D2M8K2.t7563 from rfl, allE_node, rows7562, irow7555, rows7563]
  all_goals rfl

theorem atot7555 : totK PD2M8K2 D2M8K2.u7555 = [0, 319007465484, 893411955885, 568462048271, 51994543477, 0, 0, 0] := by
  rw [show D2M8K2.u7555 = KTree.node D2M8K2.t7562 (nat_lit 16026347) (nat_lit 2902754041) (nat_lit 0) D2M8K2.t7563 from rfl, totK_node, tot7562, tot7563]
  decide +kernel

theorem arows7557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7557 = true := by
  rw [show D2M8K2.u7557 = KTree.node D2M8K2.t7564 (nat_lit 16028044) (nat_lit 3878591064) (nat_lit 0) D2M8K2.t7565 from rfl, allE_node, rows7564, irow7557, rows7565]
  all_goals rfl

theorem atot7557 : totK PD2M8K2 D2M8K2.u7557 = [0, 0, 406018258148, 963546365533, 388433232242, 20058171799, 0, 0] := by
  rw [show D2M8K2.u7557 = KTree.node D2M8K2.t7564 (nat_lit 16028044) (nat_lit 3878591064) (nat_lit 0) D2M8K2.t7565 from rfl, totK_node, tot7564, tot7565]
  decide +kernel

theorem arows7558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7558 = true := by
  rw [show D2M8K2.u7558 = KTree.node D2M8K2.t7566 (nat_lit 16029917) (nat_lit 1628904275) (nat_lit 0) D2M8K2.t7567 from rfl, allE_node, rows7566, irow7558, rows7567]
  all_goals rfl

theorem atot7558 : totK PD2M8K2 D2M8K2.u7558 = [0, 0, 377322845585, 961392789422, 401961957412, 16080396318, 0, 0] := by
  rw [show D2M8K2.u7558 = KTree.node D2M8K2.t7566 (nat_lit 16029917) (nat_lit 1628904275) (nat_lit 0) D2M8K2.t7567 from rfl, totK_node, tot7566, tot7567]
  decide +kernel

theorem arows7562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7562 = true := by
  rw [show D2M8K2.u7562 = KTree.node D2M8K2.t7568 (nat_lit 16031837) (nat_lit 2227354491) (nat_lit 0) D2M8K2.t7569 from rfl, allE_node, rows7568, irow7562, rows7569]
  all_goals rfl

theorem atot7562 : totK PD2M8K2 D2M8K2.u7562 = [0, 0, 107608872648, 692817685527, 828687808293, 125652373382, 1206465782, 0] := by
  rw [show D2M8K2.u7562 = KTree.node D2M8K2.t7568 (nat_lit 16031837) (nat_lit 2227354491) (nat_lit 0) D2M8K2.t7569 from rfl, totK_node, tot7568, tot7569]
  decide +kernel

theorem arows7563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7563 = true := by
  rw [show D2M8K2.u7563 = KTree.node D2M8K2.t7570 (nat_lit 16033634) (nat_lit 4086183302) (nat_lit 0) D2M8K2.t7571 from rfl, allE_node, rows7570, irow7563, rows7571]
  all_goals rfl

theorem atot7563 : totK PD2M8K2 D2M8K2.u7563 = [0, 0, 403434644743, 968202801867, 421197558489, 22530046025, 0, 0] := by
  rw [show D2M8K2.u7563 = KTree.node D2M8K2.t7570 (nat_lit 16033634) (nat_lit 4086183302) (nat_lit 0) D2M8K2.t7571 from rfl, totK_node, tot7570, tot7571]
  decide +kernel

theorem arows7565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7565 = true := by
  rw [show D2M8K2.u7565 = KTree.node D2M8K2.t7572 (nat_lit 16036587) (nat_lit 3710019890) (nat_lit 0) D2M8K2.t7573 from rfl, allE_node, rows7572, irow7565, rows7573]
  all_goals rfl

theorem atot7565 : totK PD2M8K2 D2M8K2.u7565 = [0, 0, 358111007062, 952533687045, 482212561035, 29493776514, 0, 0] := by
  rw [show D2M8K2.u7565 = KTree.node D2M8K2.t7572 (nat_lit 16036587) (nat_lit 3710019890) (nat_lit 0) D2M8K2.t7573 from rfl, totK_node, tot7572, tot7573]
  decide +kernel

theorem arows7566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7566 = true := by
  rw [show D2M8K2.u7566 = KTree.node D2M8K2.t7574 (nat_lit 16038274) (nat_lit 4114527027) (nat_lit 0) D2M8K2.t7575 from rfl, allE_node, rows7574, irow7566, rows7575]
  all_goals rfl

theorem atot7566 : totK PD2M8K2 D2M8K2.u7566 = [0, 0, 36272210802, 503468204833, 903288628169, 278863695452, 13016197374, 0] := by
  rw [show D2M8K2.u7566 = KTree.node D2M8K2.t7574 (nat_lit 16038274) (nat_lit 4114527027) (nat_lit 0) D2M8K2.t7575 from rfl, totK_node, tot7574, tot7575]
  decide +kernel

theorem arows7569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7569 = true := by
  rw [show D2M8K2.u7569 = KTree.node D2M8K2.t7576 (nat_lit 16043424) (nat_lit 3511525208) (nat_lit 0) D2M8K2.t7577 from rfl, allE_node, rows7576, irow7569, rows7577]
  all_goals rfl

theorem atot7569 : totK PD2M8K2 D2M8K2.u7569 = [0, 0, 380862122060, 945913890142, 430685642561, 24200525243, 0, 0] := by
  rw [show D2M8K2.u7569 = KTree.node D2M8K2.t7576 (nat_lit 16043424) (nat_lit 3511525208) (nat_lit 0) D2M8K2.t7577 from rfl, totK_node, tot7576, tot7577]
  decide +kernel

theorem arows7570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7570 = true := by
  rw [show D2M8K2.u7570 = KTree.node D2M8K2.t7578 (nat_lit 16045193) (nat_lit 1582980476) (nat_lit 0) D2M8K2.t7579 from rfl, allE_node, rows7578, irow7570, rows7579]
  all_goals rfl

theorem atot7570 : totK PD2M8K2 D2M8K2.u7570 = [0, 0, 84568401081, 665780259725, 792393669524, 152838964140, 4574395652, 0] := by
  rw [show D2M8K2.u7570 = KTree.node D2M8K2.t7578 (nat_lit 16045193) (nat_lit 1582980476) (nat_lit 0) D2M8K2.t7579 from rfl, totK_node, tot7578, tot7579]
  decide +kernel

theorem arows7572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7572 = true := by
  rw [show D2M8K2.u7572 = KTree.node D2M8K2.t7580 (nat_lit 16047048) (nat_lit 3434090403) (nat_lit 0) D2M8K2.t7581 from rfl, allE_node, rows7580, irow7572, rows7581]
  all_goals rfl

theorem atot7572 : totK PD2M8K2 D2M8K2.u7572 = [0, 37052073317, 380148636476, 886850491738, 488875014475, 39517771004, 0, 0] := by
  rw [show D2M8K2.u7572 = KTree.node D2M8K2.t7580 (nat_lit 16047048) (nat_lit 3434090403) (nat_lit 0) D2M8K2.t7581 from rfl, totK_node, tot7580, tot7581]
  decide +kernel

theorem arows7573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7573 = true := by
  rw [show D2M8K2.u7573 = KTree.node D2M8K2.t7582 (nat_lit 16092100) (nat_lit 2864752617) (nat_lit 0) D2M8K2.t7583 from rfl, allE_node, rows7582, irow7573, rows7583]
  all_goals rfl

theorem atot7573 : totK PD2M8K2 D2M8K2.u7573 = [0, 369122772807, 936557051535, 435757084885, 23648084212, 0, 0, 0] := by
  rw [show D2M8K2.u7573 = KTree.node D2M8K2.t7582 (nat_lit 16092100) (nat_lit 2864752617) (nat_lit 0) D2M8K2.t7583 from rfl, totK_node, tot7582, tot7583]
  decide +kernel

theorem arows7578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7578 = true := by
  rw [show D2M8K2.u7578 = KTree.node D2M8K2.t7584 (nat_lit 16093829) (nat_lit 1990427199) (nat_lit 0) D2M8K2.t7585 from rfl, allE_node, rows7584, irow7578, rows7585]
  all_goals rfl

theorem atot7578 : totK PD2M8K2 D2M8K2.u7578 = [0, 92923763202, 656721303533, 886228710074, 158491911413, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7578 = KTree.node D2M8K2.t7584 (nat_lit 16093829) (nat_lit 1990427199) (nat_lit 0) D2M8K2.t7585 from rfl, totK_node, tot7584, tot7585]
  decide +kernel

theorem arows7579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7579 = true := by
  rw [show D2M8K2.u7579 = KTree.node D2M8K2.t7586 (nat_lit 16095723) (nat_lit 3468146575) (nat_lit 0) D2M8K2.t7587 from rfl, allE_node, rows7586, irow7579, rows7587]
  all_goals rfl

theorem atot7579 : totK PD2M8K2 D2M8K2.u7579 = [0, 324540398817, 901767194043, 548103296349, 51109394260, 0, 0, 0] := by
  rw [show D2M8K2.u7579 = KTree.node D2M8K2.t7586 (nat_lit 16095723) (nat_lit 3468146575) (nat_lit 0) D2M8K2.t7587 from rfl, totK_node, tot7586, tot7587]
  decide +kernel

theorem arows7581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7581 = true := by
  rw [show D2M8K2.u7581 = KTree.node D2M8K2.t7588 (nat_lit 16097259) (nat_lit 3675647139) (nat_lit 0) D2M8K2.t7589 from rfl, allE_node, rows7588, irow7581, rows7589]
  all_goals rfl

theorem atot7581 : totK PD2M8K2 D2M8K2.u7581 = [0, 0, 375566309486, 945728987892, 457770334837, 30547157478, 0, 0] := by
  rw [show D2M8K2.u7581 = KTree.node D2M8K2.t7588 (nat_lit 16097259) (nat_lit 3675647139) (nat_lit 0) D2M8K2.t7589 from rfl, totK_node, tot7588, tot7589]
  decide +kernel

theorem arows7582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7582 = true := by
  rw [show D2M8K2.u7582 = KTree.node D2M8K2.t7590 (nat_lit 16098570) (nat_lit 3521555521) (nat_lit 0) D2M8K2.t7591 from rfl, allE_node, rows7590, irow7582, rows7591]
  all_goals rfl

theorem atot7582 : totK PD2M8K2 D2M8K2.u7582 = [0, 353870518770, 871350178855, 479996460126, 104385342859, 5354502914, 0, 0] := by
  rw [show D2M8K2.u7582 = KTree.node D2M8K2.t7590 (nat_lit 16098570) (nat_lit 3521555521) (nat_lit 0) D2M8K2.t7591 from rfl, totK_node, tot7590, tot7591]
  decide +kernel

theorem arows7585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7585 = true := by
  rw [show D2M8K2.u7585 = KTree.node D2M8K2.t7592 (nat_lit 16100123) (nat_lit 2757209985) (nat_lit 0) D2M8K2.t7593 from rfl, allE_node, rows7592, irow7585, rows7593]
  all_goals rfl

theorem atot7585 : totK PD2M8K2 D2M8K2.u7585 = [0, 72493291087, 569745977927, 886247283456, 248198773902, 10568566766, 0, 0] := by
  rw [show D2M8K2.u7585 = KTree.node D2M8K2.t7592 (nat_lit 16100123) (nat_lit 2757209985) (nat_lit 0) D2M8K2.t7593 from rfl, totK_node, tot7592, tot7593]
  decide +kernel

theorem arows7586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7586 = true := by
  rw [show D2M8K2.u7586 = KTree.node D2M8K2.t7594 (nat_lit 16101962) (nat_lit 4267463172) (nat_lit 0) D2M8K2.t7595 from rfl, allE_node, rows7594, irow7586, rows7595]
  all_goals rfl

theorem atot7586 : totK PD2M8K2 D2M8K2.u7586 = [0, 323621509918, 886373643110, 512818947495, 71829246395, 2481160468, 0, 0] := by
  rw [show D2M8K2.u7586 = KTree.node D2M8K2.t7594 (nat_lit 16101962) (nat_lit 4267463172) (nat_lit 0) D2M8K2.t7595 from rfl, totK_node, tot7594, tot7595]
  decide +kernel

theorem arows7588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7588 = true := by
  rw [show D2M8K2.u7588 = KTree.node D2M8K2.t7596 (nat_lit 16104429) (nat_lit 1464322445) (nat_lit 0) D2M8K2.t7597 from rfl, allE_node, rows7596, irow7588, rows7597]
  all_goals rfl

theorem atot7588 : totK PD2M8K2 D2M8K2.u7588 = [0, 163880098198, 666767309784, 774355393062, 173561378062, 4780023221, 0, 0] := by
  rw [show D2M8K2.u7588 = KTree.node D2M8K2.t7596 (nat_lit 16104429) (nat_lit 1464322445) (nat_lit 0) D2M8K2.t7597 from rfl, totK_node, tot7596, tot7597]
  decide +kernel

theorem arows7589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7589 = true := by
  rw [show D2M8K2.u7589 = KTree.node D2M8K2.t7598 (nat_lit 16105936) (nat_lit 2809303705) (nat_lit 0) D2M8K2.t7599 from rfl, allE_node, rows7598, irow7589, rows7599]
  all_goals rfl

theorem atot7589 : totK PD2M8K2 D2M8K2.u7589 = [0, 274002740752, 862901749730, 609806411365, 61550598015, 0, 0, 0] := by
  rw [show D2M8K2.u7589 = KTree.node D2M8K2.t7598 (nat_lit 16105936) (nat_lit 2809303705) (nat_lit 0) D2M8K2.t7599 from rfl, totK_node, tot7598, tot7599]
  decide +kernel

theorem arows7593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7593 = true := by
  rw [show D2M8K2.u7593 = KTree.node D2M8K2.t7600 (nat_lit 16107885) (nat_lit 1493167766) (nat_lit 0) D2M8K2.t7601 from rfl, allE_node, rows7600, irow7593, rows7601]
  all_goals rfl

theorem atot7593 : totK PD2M8K2 D2M8K2.u7593 = [0, 0, 507106436398, 1015196841922, 278103479022, 6350335412, 0, 0] := by
  rw [show D2M8K2.u7593 = KTree.node D2M8K2.t7600 (nat_lit 16107885) (nat_lit 1493167766) (nat_lit 0) D2M8K2.t7601 from rfl, totK_node, tot7600, tot7601]
  decide +kernel

theorem arows7594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7594 = true := by
  rw [show D2M8K2.u7594 = KTree.node D2M8K2.t7602 (nat_lit 16113180) (nat_lit 3082743799) (nat_lit 0) D2M8K2.t7603 from rfl, allE_node, rows7602, irow7594, rows7603]
  all_goals rfl

theorem atot7594 : totK PD2M8K2 D2M8K2.u7594 = [0, 0, 245734369512, 827327688126, 560092747755, 66736045780, 1138244013, 0] := by
  rw [show D2M8K2.u7594 = KTree.node D2M8K2.t7602 (nat_lit 16113180) (nat_lit 3082743799) (nat_lit 0) D2M8K2.t7603 from rfl, totK_node, tot7602, tot7603]
  decide +kernel

theorem arows7596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7596 = true := by
  rw [show D2M8K2.u7596 = KTree.node D2M8K2.t7604 (nat_lit 16115802) (nat_lit 3679100857) (nat_lit 0) D2M8K2.t7605 from rfl, allE_node, rows7604, irow7596, rows7605]
  all_goals rfl

theorem atot7596 : totK PD2M8K2 D2M8K2.u7596 = [0, 0, 258613890392, 872543814526, 599628632314, 54858228332, 0, 0] := by
  rw [show D2M8K2.u7596 = KTree.node D2M8K2.t7604 (nat_lit 16115802) (nat_lit 3679100857) (nat_lit 0) D2M8K2.t7605 from rfl, totK_node, tot7604, tot7605]
  decide +kernel

theorem arows7597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7597 = true := by
  rw [show D2M8K2.u7597 = KTree.node D2M8K2.t7606 (nat_lit 16118843) (nat_lit 2722540328) (nat_lit 0) D2M8K2.t7607 from rfl, allE_node, rows7606, irow7597, rows7607]
  all_goals rfl

theorem atot7597 : totK PD2M8K2 D2M8K2.u7597 = [0, 0, 386263737619, 966996240891, 442723699552, 20697018838, 0, 0] := by
  rw [show D2M8K2.u7597 = KTree.node D2M8K2.t7606 (nat_lit 16118843) (nat_lit 2722540328) (nat_lit 0) D2M8K2.t7607 from rfl, totK_node, tot7606, tot7607]
  decide +kernel

theorem arows7600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7600 = true := by
  rw [show D2M8K2.u7600 = KTree.node D2M8K2.t7608 (nat_lit 16120357) (nat_lit 1347083685) (nat_lit 0) D2M8K2.t7609 from rfl, allE_node, rows7608, irow7600, rows7609]
  all_goals rfl

theorem atot7600 : totK PD2M8K2 D2M8K2.u7600 = [0, 0, 359303880616, 958044738994, 444811247775, 20894046726, 0, 0] := by
  rw [show D2M8K2.u7600 = KTree.node D2M8K2.t7608 (nat_lit 16120357) (nat_lit 1347083685) (nat_lit 0) D2M8K2.t7609 from rfl, totK_node, tot7608, tot7609]
  decide +kernel

theorem arows7601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7601 = true := by
  rw [show D2M8K2.u7601 = KTree.node D2M8K2.t7610 (nat_lit 16125774) (nat_lit 3982008099) (nat_lit 0) D2M8K2.t7611 from rfl, allE_node, rows7610, irow7601, rows7611]
  all_goals rfl

theorem atot7601 : totK PD2M8K2 D2M8K2.u7601 = [0, 0, 395244530254, 946546425676, 430109436283, 22775935453, 0, 0] := by
  rw [show D2M8K2.u7601 = KTree.node D2M8K2.t7610 (nat_lit 16125774) (nat_lit 3982008099) (nat_lit 0) D2M8K2.t7611 from rfl, totK_node, tot7610, tot7611]
  decide +kernel

theorem arows7603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7603 = true := by
  rw [show D2M8K2.u7603 = KTree.node D2M8K2.t7612 (nat_lit 16126956) (nat_lit 3185297290) (nat_lit 0) D2M8K2.t7613 from rfl, allE_node, rows7612, irow7603, rows7613]
  all_goals rfl

theorem atot7603 : totK PD2M8K2 D2M8K2.u7603 = [0, 0, 199633593617, 792416413742, 651340998586, 87928733270, 1095107716, 0] := by
  rw [show D2M8K2.u7603 = KTree.node D2M8K2.t7612 (nat_lit 16126956) (nat_lit 3185297290) (nat_lit 0) D2M8K2.t7613 from rfl, totK_node, tot7612, tot7613]
  decide +kernel

theorem arows7604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7604 = true := by
  rw [show D2M8K2.u7604 = KTree.node D2M8K2.t7614 (nat_lit 16132742) (nat_lit 3297023986) (nat_lit 0) D2M8K2.t7615 from rfl, allE_node, rows7614, irow7604, rows7615]
  all_goals rfl

theorem atot7604 : totK PD2M8K2 D2M8K2.u7604 = [0, 252651705119, 605204811580, 454930967150, 354207411365, 94540414338, 3882006667, 0] := by
  rw [show D2M8K2.u7604 = KTree.node D2M8K2.t7614 (nat_lit 16132742) (nat_lit 3297023986) (nat_lit 0) D2M8K2.t7615 from rfl, totK_node, tot7614, tot7615]
  decide +kernel

theorem arows7610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7610 = true := by
  rw [show D2M8K2.u7610 = KTree.node D2M8K2.t7616 (nat_lit 16134342) (nat_lit 3779087480) (nat_lit 0) D2M8K2.t7617 from rfl, allE_node, rows7616, irow7610, rows7617]
  all_goals rfl

theorem atot7610 : totK PD2M8K2 D2M8K2.u7610 = [0, 154963680961, 719139422592, 774777348730, 128697933212, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7610 = KTree.node D2M8K2.t7616 (nat_lit 16134342) (nat_lit 3779087480) (nat_lit 0) D2M8K2.t7617 from rfl, totK_node, tot7616, tot7617]
  decide +kernel

theorem arows7611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7611 = true := by
  rw [show D2M8K2.u7611 = KTree.node D2M8K2.t7618 (nat_lit 16136672) (nat_lit 3672933527) (nat_lit 0) D2M8K2.t7619 from rfl, allE_node, rows7618, irow7611, rows7619]
  all_goals rfl

theorem atot7611 : totK PD2M8K2 D2M8K2.u7611 = [0, 308004589899, 855020374447, 603903219192, 64900242434, 0, 0, 0] := by
  rw [show D2M8K2.u7611 = KTree.node D2M8K2.t7618 (nat_lit 16136672) (nat_lit 3672933527) (nat_lit 0) D2M8K2.t7619 from rfl, totK_node, tot7618, tot7619]
  decide +kernel

theorem arows7613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7613 = true := by
  rw [show D2M8K2.u7613 = KTree.node D2M8K2.t7620 (nat_lit 16138218) (nat_lit 3775134990) (nat_lit 0) D2M8K2.t7621 from rfl, allE_node, rows7620, irow7613, rows7621]
  all_goals rfl

theorem atot7613 : totK PD2M8K2 D2M8K2.u7613 = [0, 107917641086, 603323270098, 786078848067, 302979498359, 25123945117, 0, 0] := by
  rw [show D2M8K2.u7613 = KTree.node D2M8K2.t7620 (nat_lit 16138218) (nat_lit 3775134990) (nat_lit 0) D2M8K2.t7621 from rfl, totK_node, tot7620, tot7621]
  decide +kernel

theorem arows7614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7614 = true := by
  rw [show D2M8K2.u7614 = KTree.node D2M8K2.t7622 (nat_lit 16139526) (nat_lit 3457163847) (nat_lit 0) D2M8K2.t7623 from rfl, allE_node, rows7622, irow7614, rows7623]
  all_goals rfl

theorem atot7614 : totK PD2M8K2 D2M8K2.u7614 = [0, 190904563073, 621203452624, 718932675229, 275264834476, 10884197455, 0, 0] := by
  rw [show D2M8K2.u7614 = KTree.node D2M8K2.t7622 (nat_lit 16139526) (nat_lit 3457163847) (nat_lit 0) D2M8K2.t7623 from rfl, totK_node, tot7622, tot7623]
  decide +kernel

theorem arows7617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7617 = true := by
  rw [show D2M8K2.u7617 = KTree.node D2M8K2.t7624 (nat_lit 16141025) (nat_lit 2213229743) (nat_lit 0) D2M8K2.t7625 from rfl, allE_node, rows7624, irow7617, rows7625]
  all_goals rfl

theorem atot7617 : totK PD2M8K2 D2M8K2.u7617 = [0, 236084612547, 801612070880, 673838910710, 105061091899, 1164319620, 0, 0] := by
  rw [show D2M8K2.u7617 = KTree.node D2M8K2.t7624 (nat_lit 16141025) (nat_lit 2213229743) (nat_lit 0) D2M8K2.t7625 from rfl, totK_node, tot7624, tot7625]
  decide +kernel

theorem arows7618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7618 = true := by
  rw [show D2M8K2.u7618 = KTree.node D2M8K2.t7626 (nat_lit 16142734) (nat_lit 3976042138) (nat_lit 0) D2M8K2.t7627 from rfl, allE_node, rows7626, irow7618, rows7627]
  all_goals rfl

theorem atot7618 : totK PD2M8K2 D2M8K2.u7618 = [0, 164801163194, 646082578252, 749809758032, 223115129930, 11879463720, 0, 0] := by
  rw [show D2M8K2.u7618 = KTree.node D2M8K2.t7626 (nat_lit 16142734) (nat_lit 3976042138) (nat_lit 0) D2M8K2.t7627 from rfl, totK_node, tot7626, tot7627]
  decide +kernel

theorem arows7620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7620 = true := by
  rw [show D2M8K2.u7620 = KTree.node D2M8K2.t7628 (nat_lit 16144710) (nat_lit 3815884324) (nat_lit 0) D2M8K2.t7629 from rfl, allE_node, rows7628, irow7620, rows7629]
  all_goals rfl

theorem atot7620 : totK PD2M8K2 D2M8K2.u7620 = [0, 161889032206, 679312475515, 774555882274, 178416646697, 5455647540, 0, 0] := by
  rw [show D2M8K2.u7620 = KTree.node D2M8K2.t7628 (nat_lit 16144710) (nat_lit 3815884324) (nat_lit 0) D2M8K2.t7629 from rfl, totK_node, tot7628, tot7629]
  decide +kernel

theorem arows7621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7621 = true := by
  rw [show D2M8K2.u7621 = KTree.node D2M8K2.t7630 (nat_lit 16150315) (nat_lit 1594385462) (nat_lit 0) D2M8K2.t7631 from rfl, allE_node, rows7630, irow7621, rows7631]
  all_goals rfl

theorem atot7621 : totK PD2M8K2 D2M8K2.u7621 = [0, 348080731256, 891555604734, 539754476187, 64857894064, 0, 0, 0] := by
  rw [show D2M8K2.u7621 = KTree.node D2M8K2.t7630 (nat_lit 16150315) (nat_lit 1594385462) (nat_lit 0) D2M8K2.t7631 from rfl, totK_node, tot7630, tot7631]
  decide +kernel

theorem arows7625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7625 = true := by
  rw [show D2M8K2.u7625 = KTree.node D2M8K2.t7632 (nat_lit 16151761) (nat_lit 1547233925) (nat_lit 0) D2M8K2.t7633 from rfl, allE_node, rows7632, irow7625, rows7633]
  all_goals rfl

theorem atot7625 : totK PD2M8K2 D2M8K2.u7625 = [0, 93763323609, 629277655753, 865826191931, 214210986634, 4967996017, 0, 0] := by
  rw [show D2M8K2.u7625 = KTree.node D2M8K2.t7632 (nat_lit 16151761) (nat_lit 1547233925) (nat_lit 0) D2M8K2.t7633 from rfl, totK_node, tot7632, tot7633]
  decide +kernel

theorem arows7626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7626 = true := by
  rw [show D2M8K2.u7626 = KTree.node D2M8K2.t7634 (nat_lit 16153436) (nat_lit 3023977101) (nat_lit 0) D2M8K2.t7635 from rfl, allE_node, rows7634, irow7626, rows7635]
  all_goals rfl

theorem atot7626 : totK PD2M8K2 D2M8K2.u7626 = [0, 0, 392330715686, 955691687644, 408514436750, 22416853141, 0, 0] := by
  rw [show D2M8K2.u7626 = KTree.node D2M8K2.t7634 (nat_lit 16153436) (nat_lit 3023977101) (nat_lit 0) D2M8K2.t7635 from rfl, totK_node, tot7634, tot7635]
  decide +kernel

theorem arows7628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7628 = true := by
  rw [show D2M8K2.u7628 = KTree.node D2M8K2.t7636 (nat_lit 16155073) (nat_lit 1575612183) (nat_lit 0) D2M8K2.t7637 from rfl, allE_node, rows7636, irow7628, rows7637]
  all_goals rfl

theorem atot7628 : totK PD2M8K2 D2M8K2.u7628 = [0, 0, 154385446764, 753404740610, 733980360606, 91848240831, 1310285577, 0] := by
  rw [show D2M8K2.u7628 = KTree.node D2M8K2.t7636 (nat_lit 16155073) (nat_lit 1575612183) (nat_lit 0) D2M8K2.t7637 from rfl, totK_node, tot7636, tot7637]
  decide +kernel

theorem arows7629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7629 = true := by
  rw [show D2M8K2.u7629 = KTree.node D2M8K2.t7638 (nat_lit 16157436) (nat_lit 3072102634) (nat_lit 0) D2M8K2.t7639 from rfl, allE_node, rows7638, irow7629, rows7639]
  all_goals rfl

theorem atot7629 : totK PD2M8K2 D2M8K2.u7629 = [0, 0, 328247348096, 888999861907, 568189626246, 48443063884, 0, 0] := by
  rw [show D2M8K2.u7629 = KTree.node D2M8K2.t7638 (nat_lit 16157436) (nat_lit 3072102634) (nat_lit 0) D2M8K2.t7639 from rfl, totK_node, tot7638, tot7639]
  decide +kernel

theorem arows7632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7632 = true := by
  rw [show D2M8K2.u7632 = KTree.node D2M8K2.t7640 (nat_lit 16160498) (nat_lit 2283330773) (nat_lit 0) D2M8K2.t7641 from rfl, allE_node, rows7640, irow7632, rows7641]
  all_goals rfl

theorem atot7632 : totK PD2M8K2 D2M8K2.u7632 = [0, 0, 354087427945, 923230837962, 505552909338, 39741567928, 0, 0] := by
  rw [show D2M8K2.u7632 = KTree.node D2M8K2.t7640 (nat_lit 16160498) (nat_lit 2283330773) (nat_lit 0) D2M8K2.t7641 from rfl, totK_node, tot7640, tot7641]
  decide +kernel

theorem arows7633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7633 = true := by
  rw [show D2M8K2.u7633 = KTree.node D2M8K2.t7642 (nat_lit 16161993) (nat_lit 1728044093) (nat_lit 0) D2M8K2.t7643 from rfl, allE_node, rows7642, irow7633, rows7643]
  all_goals rfl

theorem atot7633 : totK PD2M8K2 D2M8K2.u7633 = [0, 0, 160519261082, 700583307388, 746829919106, 150074390127, 4879840392, 0] := by
  rw [show D2M8K2.u7633 = KTree.node D2M8K2.t7642 (nat_lit 16161993) (nat_lit 1728044093) (nat_lit 0) D2M8K2.t7643 from rfl, totK_node, tot7642, tot7643]
  decide +kernel

theorem arows7635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7635 = true := by
  rw [show D2M8K2.u7635 = KTree.node D2M8K2.t7644 (nat_lit 16164079) (nat_lit 2430501014) (nat_lit 0) D2M8K2.t7645 from rfl, allE_node, rows7644, irow7635, rows7645]
  all_goals rfl

theorem atot7635 : totK PD2M8K2 D2M8K2.u7635 = [0, 0, 309688604792, 871484648044, 565261297702, 56232624784, 0, 0] := by
  rw [show D2M8K2.u7635 = KTree.node D2M8K2.t7644 (nat_lit 16164079) (nat_lit 2430501014) (nat_lit 0) D2M8K2.t7645 from rfl, totK_node, tot7644, tot7645]
  decide +kernel

theorem arows7636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7636 = true := by
  rw [show D2M8K2.u7636 = KTree.node D2M8K2.t7646 (nat_lit 16171084) (nat_lit 3843887223) (nat_lit 0) D2M8K2.t7647 from rfl, allE_node, rows7646, irow7636, rows7647]
  all_goals rfl

theorem atot7636 : totK PD2M8K2 D2M8K2.u7636 = [0, 0, 358556991364, 928283330834, 494826770620, 39725448268, 0, 0] := by
  rw [show D2M8K2.u7636 = KTree.node D2M8K2.t7646 (nat_lit 16171084) (nat_lit 3843887223) (nat_lit 0) D2M8K2.t7647 from rfl, totK_node, tot7646, tot7647]
  decide +kernel

theorem arows7641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7641 = true := by
  rw [show D2M8K2.u7641 = KTree.node D2M8K2.t7648 (nat_lit 16172509) (nat_lit 1242138600) (nat_lit 0) D2M8K2.t7649 from rfl, allE_node, rows7648, irow7641, rows7649]
  all_goals rfl

theorem atot7641 : totK PD2M8K2 D2M8K2.u7641 = [0, 0, 93578216757, 653042962739, 837326499414, 182744534257, 4811815119, 0] := by
  rw [show D2M8K2.u7641 = KTree.node D2M8K2.t7648 (nat_lit 16172509) (nat_lit 1242138600) (nat_lit 0) D2M8K2.t7649 from rfl, totK_node, tot7648, tot7649]
  decide +kernel

theorem arows7642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7642 = true := by
  rw [show D2M8K2.u7642 = KTree.node D2M8K2.t7650 (nat_lit 16174685) (nat_lit 2315579421) (nat_lit 0) D2M8K2.t7651 from rfl, allE_node, rows7650, irow7642, rows7651]
  all_goals rfl

theorem atot7642 : totK PD2M8K2 D2M8K2.u7642 = [0, 0, 304091876416, 805802704991, 540527069632, 126015351665, 8974678929, 0] := by
  rw [show D2M8K2.u7642 = KTree.node D2M8K2.t7650 (nat_lit 16174685) (nat_lit 2315579421) (nat_lit 0) D2M8K2.t7651 from rfl, totK_node, tot7650, tot7651]
  decide +kernel

theorem arows7644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7644 = true := by
  rw [show D2M8K2.u7644 = KTree.node D2M8K2.t7652 (nat_lit 16175904) (nat_lit 3619169329) (nat_lit 0) D2M8K2.t7653 from rfl, allE_node, rows7652, irow7644, rows7653]
  all_goals rfl

theorem atot7644 : totK PD2M8K2 D2M8K2.u7644 = [0, 0, 126751692978, 727978270552, 806288134258, 121386534910, 1369150432, 0] := by
  rw [show D2M8K2.u7644 = KTree.node D2M8K2.t7652 (nat_lit 16175904) (nat_lit 3619169329) (nat_lit 0) D2M8K2.t7653 from rfl, totK_node, tot7652, tot7653]
  decide +kernel

theorem arows7645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7645 = true := by
  rw [show D2M8K2.u7645 = KTree.node D2M8K2.t7654 (nat_lit 16181475) (nat_lit 3673659104) (nat_lit 0) D2M8K2.t7655 from rfl, allE_node, rows7654, irow7645, rows7655]
  all_goals rfl

theorem atot7645 : totK PD2M8K2 D2M8K2.u7645 = [0, 0, 336858817701, 897390496491, 532257920344, 42818815062, 0, 0] := by
  rw [show D2M8K2.u7645 = KTree.node D2M8K2.t7654 (nat_lit 16181475) (nat_lit 3673659104) (nat_lit 0) D2M8K2.t7655 from rfl, totK_node, tot7654, tot7655]
  decide +kernel

theorem arows7648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7648 = true := by
  rw [show D2M8K2.u7648 = KTree.node D2M8K2.t7656 (nat_lit 16182986) (nat_lit 3023222527) (nat_lit 0) D2M8K2.t7657 from rfl, allE_node, rows7656, irow7648, rows7657]
  all_goals rfl

theorem atot7648 : totK PD2M8K2 D2M8K2.u7648 = [0, 0, 86420403140, 601266449489, 861644263071, 222118556440, 9587713104, 0] := by
  rw [show D2M8K2.u7648 = KTree.node D2M8K2.t7656 (nat_lit 16182986) (nat_lit 3023222527) (nat_lit 0) D2M8K2.t7657 from rfl, totK_node, tot7656, tot7657]
  decide +kernel

theorem arows7649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7649 = true := by
  rw [show D2M8K2.u7649 = KTree.node D2M8K2.t7658 (nat_lit 16185422) (nat_lit 2916584876) (nat_lit 0) D2M8K2.t7659 from rfl, allE_node, rows7658, irow7649, rows7659]
  all_goals rfl

theorem atot7649 : totK PD2M8K2 D2M8K2.u7649 = [0, 0, 320256372558, 863183714806, 491547142940, 80084093728, 3462014130, 0] := by
  rw [show D2M8K2.u7649 = KTree.node D2M8K2.t7658 (nat_lit 16185422) (nat_lit 2916584876) (nat_lit 0) D2M8K2.t7659 from rfl, totK_node, tot7658, tot7659]
  decide +kernel

theorem arows7651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7651 = true := by
  rw [show D2M8K2.u7651 = KTree.node D2M8K2.t7660 (nat_lit 16187737) (nat_lit 1489021467) (nat_lit 0) D2M8K2.t7661 from rfl, allE_node, rows7660, irow7651, rows7661]
  all_goals rfl

theorem atot7651 : totK PD2M8K2 D2M8K2.u7651 = [0, 0, 189013423629, 781151907573, 705163886273, 80841655102, 1198073392, 0] := by
  rw [show D2M8K2.u7651 = KTree.node D2M8K2.t7660 (nat_lit 16187737) (nat_lit 1489021467) (nat_lit 0) D2M8K2.t7661 from rfl, totK_node, tot7660, tot7661]
  decide +kernel

theorem arows7652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7652 = true := by
  rw [show D2M8K2.u7652 = KTree.node D2M8K2.t7662 (nat_lit 16189141) (nat_lit 1250220224) (nat_lit 0) D2M8K2.t7663 from rfl, allE_node, rows7662, irow7652, rows7663]
  all_goals rfl

theorem atot7652 : totK PD2M8K2 D2M8K2.u7652 = [0, 0, 217847319002, 785808659941, 655703374991, 87355034168, 1096505104, 0] := by
  rw [show D2M8K2.u7652 = KTree.node D2M8K2.t7662 (nat_lit 16189141) (nat_lit 1250220224) (nat_lit 0) D2M8K2.t7663 from rfl, totK_node, tot7662, tot7663]
  decide +kernel

theorem arows7656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7656 = true := by
  rw [show D2M8K2.u7656 = KTree.node D2M8K2.t7664 (nat_lit 16191480) (nat_lit 3631534234) (nat_lit 0) D2M8K2.t7665 from rfl, allE_node, rows7664, irow7656, rows7665]
  all_goals rfl

theorem atot7656 : totK PD2M8K2 D2M8K2.u7656 = [0, 0, 243172225384, 768911741670, 660961649415, 112029697807, 3820764243, 0] := by
  rw [show D2M8K2.u7656 = KTree.node D2M8K2.t7664 (nat_lit 16191480) (nat_lit 3631534234) (nat_lit 0) D2M8K2.t7665 from rfl, totK_node, tot7664, tot7665]
  decide +kernel

theorem arows7657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7657 = true := by
  rw [show D2M8K2.u7657 = KTree.node D2M8K2.t7666 (nat_lit 16193098) (nat_lit 3962179576) (nat_lit 0) D2M8K2.t7667 from rfl, allE_node, rows7666, irow7657, rows7667]
  all_goals rfl

theorem atot7657 : totK PD2M8K2 D2M8K2.u7657 = [0, 0, 168597656713, 696917034513, 751348785061, 169216971264, 4967996017, 0] := by
  rw [show D2M8K2.u7657 = KTree.node D2M8K2.t7666 (nat_lit 16193098) (nat_lit 3962179576) (nat_lit 0) D2M8K2.t7667 from rfl, totK_node, tot7666, tot7667]
  decide +kernel

theorem arows7659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7659 = true := by
  rw [show D2M8K2.u7659 = KTree.node D2M8K2.t7668 (nat_lit 16195010) (nat_lit 3032877523) (nat_lit 0) D2M8K2.t7669 from rfl, allE_node, rows7668, irow7659, rows7669]
  all_goals rfl

theorem atot7659 : totK PD2M8K2 D2M8K2.u7659 = [0, 0, 0, 430707848234, 955760846080, 349513705136, 19549668190, 0] := by
  rw [show D2M8K2.u7659 = KTree.node D2M8K2.t7668 (nat_lit 16195010) (nat_lit 3032877523) (nat_lit 0) D2M8K2.t7669 from rfl, totK_node, tot7668, tot7669]
  decide +kernel

theorem arows7660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7660 = true := by
  rw [show D2M8K2.u7660 = KTree.node D2M8K2.t7670 (nat_lit 16196612) (nat_lit 3068311239) (nat_lit 0) D2M8K2.t7671 from rfl, allE_node, rows7670, irow7660, rows7671]
  all_goals rfl

theorem atot7660 : totK PD2M8K2 D2M8K2.u7660 = [0, 0, 0, 159089179506, 765499231720, 660695910449, 97686004617, 1275377855] := by
  rw [show D2M8K2.u7660 = KTree.node D2M8K2.t7670 (nat_lit 16196612) (nat_lit 3068311239) (nat_lit 0) D2M8K2.t7671 from rfl, totK_node, tot7670, tot7671]
  decide +kernel

theorem arows7663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7663 = true := by
  rw [show D2M8K2.u7663 = KTree.node D2M8K2.t7672 (nat_lit 16202312) (nat_lit 3601020842) (nat_lit 0) D2M8K2.t7673 from rfl, allE_node, rows7672, irow7663, rows7673]
  all_goals rfl

theorem atot7663 : totK PD2M8K2 D2M8K2.u7663 = [0, 0, 0, 359425291296, 940035385810, 433810488780, 25328190505, 0] := by
  rw [show D2M8K2.u7663 = KTree.node D2M8K2.t7672 (nat_lit 16202312) (nat_lit 3601020842) (nat_lit 0) D2M8K2.t7673 from rfl, totK_node, tot7672, tot7673]
  decide +kernel

theorem arows7664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7664 = true := by
  rw [show D2M8K2.u7664 = KTree.node D2M8K2.t7674 (nat_lit 16206173) (nat_lit 1160499414) (nat_lit 0) D2M8K2.t7675 from rfl, allE_node, rows7674, irow7664, rows7675]
  all_goals rfl

theorem atot7664 : totK PD2M8K2 D2M8K2.u7664 = [0, 0, 0, 463006673964, 971492921986, 292606036949, 12536033187, 0] := by
  rw [show D2M8K2.u7664 = KTree.node D2M8K2.t7674 (nat_lit 16206173) (nat_lit 1160499414) (nat_lit 0) D2M8K2.t7675 from rfl, totK_node, tot7674, tot7675]
  decide +kernel

theorem arows7666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7666 = true := by
  rw [show D2M8K2.u7666 = KTree.node D2M8K2.t7676 (nat_lit 16209584) (nat_lit 3787791696) (nat_lit 0) D2M8K2.t7677 from rfl, allE_node, rows7676, irow7666, rows7677]
  all_goals rfl

theorem atot7666 : totK PD2M8K2 D2M8K2.u7666 = [0, 0, 0, 404097044507, 964807927178, 337718986242, 14581564360, 0] := by
  rw [show D2M8K2.u7666 = KTree.node D2M8K2.t7676 (nat_lit 16209584) (nat_lit 3787791696) (nat_lit 0) D2M8K2.t7677 from rfl, totK_node, tot7676, tot7677]
  decide +kernel

theorem arows7667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7667 = true := by
  rw [show D2M8K2.u7667 = KTree.node D2M8K2.t7678 (nat_lit 16213537) (nat_lit 1557828645) (nat_lit 0) D2M8K2.t7679 from rfl, allE_node, rows7678, irow7667, rows7679]
  all_goals rfl

theorem atot7667 : totK PD2M8K2 D2M8K2.u7667 = [0, 0, 94308027437, 558590825108, 869023856119, 289725627772, 14134165015, 0] := by
  rw [show D2M8K2.u7667 = KTree.node D2M8K2.t7678 (nat_lit 16213537) (nat_lit 1557828645) (nat_lit 0) D2M8K2.t7679 from rfl, totK_node, tot7678, tot7679]
  decide +kernel

theorem arows7676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7676 = true := by
  rw [show D2M8K2.u7676 = KTree.node D2M8K2.t7680 (nat_lit 16220186) (nat_lit 4241602830) (nat_lit 0) D2M8K2.t7681 from rfl, allE_node, rows7680, irow7676, rows7681]
  all_goals rfl

theorem atot7676 : totK PD2M8K2 D2M8K2.u7676 = [0, 0, 348847778691, 928933071915, 516805086837, 41780934593, 0, 0] := by
  rw [show D2M8K2.u7676 = KTree.node D2M8K2.t7680 (nat_lit 16220186) (nat_lit 4241602830) (nat_lit 0) D2M8K2.t7681 from rfl, totK_node, tot7680, tot7681]
  decide +kernel

theorem arows7677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7677 = true := by
  rw [show D2M8K2.u7677 = KTree.node D2M8K2.t7682 (nat_lit 16221699) (nat_lit 3655480701) (nat_lit 0) D2M8K2.t7683 from rfl, allE_node, rows7682, irow7677, rows7683]
  all_goals rfl

theorem atot7677 : totK PD2M8K2 D2M8K2.u7677 = [0, 0, 28526375756, 436733278043, 943228014039, 390064542958, 24683636622, 0] := by
  rw [show D2M8K2.u7677 = KTree.node D2M8K2.t7682 (nat_lit 16221699) (nat_lit 3655480701) (nat_lit 0) D2M8K2.t7683 from rfl, totK_node, tot7682, tot7683]
  decide +kernel

theorem arows7679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7679 = true := by
  rw [show D2M8K2.u7679 = KTree.node D2M8K2.t7684 (nat_lit 16223139) (nat_lit 3642048460) (nat_lit 0) D2M8K2.t7685 from rfl, allE_node, rows7684, irow7679, rows7685]
  all_goals rfl

theorem atot7679 : totK PD2M8K2 D2M8K2.u7679 = [0, 0, 377221414389, 940494364381, 467970362664, 33973595341, 0, 0] := by
  rw [show D2M8K2.u7679 = KTree.node D2M8K2.t7684 (nat_lit 16223139) (nat_lit 3642048460) (nat_lit 0) D2M8K2.t7685 from rfl, totK_node, tot7684, tot7685]
  decide +kernel

theorem arows7680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7680 = true := by
  rw [show D2M8K2.u7680 = KTree.node D2M8K2.t7686 (nat_lit 16224894) (nat_lit 3044016030) (nat_lit 0) D2M8K2.t7687 from rfl, allE_node, rows7686, irow7680, rows7687]
  all_goals rfl

theorem atot7680 : totK PD2M8K2 D2M8K2.u7680 = [0, 0, 47169066627, 590698963526, 944938788150, 219685976509, 9751947372, 0] := by
  rw [show D2M8K2.u7680 = KTree.node D2M8K2.t7686 (nat_lit 16224894) (nat_lit 3044016030) (nat_lit 0) D2M8K2.t7687 from rfl, totK_node, tot7686, tot7687]
  decide +kernel

theorem arows7683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7683 = true := by
  rw [show D2M8K2.u7683 = KTree.node D2M8K2.t7688 (nat_lit 16227315) (nat_lit 2986295984) (nat_lit 0) D2M8K2.t7689 from rfl, allE_node, rows7688, irow7683, rows7689]
  all_goals rfl

theorem atot7683 : totK PD2M8K2 D2M8K2.u7683 = [0, 0, 432032011101, 970945836133, 408045395430, 30676820795, 0, 0] := by
  rw [show D2M8K2.u7683 = KTree.node D2M8K2.t7688 (nat_lit 16227315) (nat_lit 2986295984) (nat_lit 0) D2M8K2.t7689 from rfl, totK_node, tot7688, tot7689]
  decide +kernel

theorem arows7684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7684 = true := by
  rw [show D2M8K2.u7684 = KTree.node D2M8K2.t7690 (nat_lit 16230350) (nat_lit 3801413609) (nat_lit 0) D2M8K2.t7691 from rfl, allE_node, rows7690, irow7684, rows7691]
  all_goals rfl

theorem atot7684 : totK PD2M8K2 D2M8K2.u7684 = [0, 0, 270384878708, 891718933704, 590355055757, 59232584939, 0, 0] := by
  rw [show D2M8K2.u7684 = KTree.node D2M8K2.t7690 (nat_lit 16230350) (nat_lit 3801413609) (nat_lit 0) D2M8K2.t7691 from rfl, totK_node, tot7690, tot7691]
  decide +kernel

theorem arows7686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7686 = true := by
  rw [show D2M8K2.u7686 = KTree.node D2M8K2.t7692 (nat_lit 16232837) (nat_lit 2297959885) (nat_lit 0) D2M8K2.t7693 from rfl, allE_node, rows7692, irow7686, rows7693]
  all_goals rfl

theorem atot7686 : totK PD2M8K2 D2M8K2.u7686 = [0, 0, 211845650220, 754766058545, 741037102703, 123186487455, 2813333534, 0] := by
  rw [show D2M8K2.u7686 = KTree.node D2M8K2.t7692 (nat_lit 16232837) (nat_lit 2297959885) (nat_lit 0) D2M8K2.t7693 from rfl, totK_node, tot7692, tot7693]
  decide +kernel

theorem arows7687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7687 = true := by
  rw [show D2M8K2.u7687 = KTree.node D2M8K2.t7694 (nat_lit 16234426) (nat_lit 3946002751) (nat_lit 0) D2M8K2.t7695 from rfl, allE_node, rows7694, irow7687, rows7695]
  all_goals rfl

theorem atot7687 : totK PD2M8K2 D2M8K2.u7687 = [0, 0, 203474773667, 815862777450, 704919634565, 98987861800, 1032608332, 0] := by
  rw [show D2M8K2.u7687 = KTree.node D2M8K2.t7694 (nat_lit 16234426) (nat_lit 3946002751) (nat_lit 0) D2M8K2.t7695 from rfl, totK_node, tot7694, tot7695]
  decide +kernel

theorem arows7691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7691 = true := by
  rw [show D2M8K2.u7691 = KTree.node D2M8K2.t7696 (nat_lit 16257158) (nat_lit 3213046279) (nat_lit 0) D2M8K2.t7697 from rfl, allE_node, rows7696, irow7691, rows7697]
  all_goals rfl

theorem atot7691 : totK PD2M8K2 D2M8K2.u7691 = [0, 0, 244315143868, 764254445355, 597641075672, 162339533860, 11568901818, 0] := by
  rw [show D2M8K2.u7691 = KTree.node D2M8K2.t7696 (nat_lit 16257158) (nat_lit 3213046279) (nat_lit 0) D2M8K2.t7697 from rfl, totK_node, tot7696, tot7697]
  decide +kernel

theorem arows7692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7692 = true := by
  rw [show D2M8K2.u7692 = KTree.node D2M8K2.t7698 (nat_lit 16258752) (nat_lit 3766812078) (nat_lit 0) D2M8K2.t7699 from rfl, allE_node, rows7698, irow7692, rows7699]
  all_goals rfl

theorem atot7692 : totK PD2M8K2 D2M8K2.u7692 = [0, 0, 169789109226, 737084210265, 739955863965, 111726106649, 1334361349, 0] := by
  rw [show D2M8K2.u7692 = KTree.node D2M8K2.t7698 (nat_lit 16258752) (nat_lit 3766812078) (nat_lit 0) D2M8K2.t7699 from rfl, totK_node, tot7698, tot7699]
  decide +kernel

theorem arows7694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7694 = true := by
  rw [show D2M8K2.u7694 = KTree.node D2M8K2.t7700 (nat_lit 16261086) (nat_lit 3384615764) (nat_lit 0) D2M8K2.t7701 from rfl, allE_node, rows7700, irow7694, rows7701]
  all_goals rfl

theorem atot7694 : totK PD2M8K2 D2M8K2.u7694 = [0, 0, 336733642539, 865252185118, 574267876043, 55371081587, 0, 0] := by
  rw [show D2M8K2.u7694 = KTree.node D2M8K2.t7700 (nat_lit 16261086) (nat_lit 3384615764) (nat_lit 0) D2M8K2.t7701 from rfl, totK_node, tot7700, tot7701]
  decide +kernel

theorem arows7695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7695 = true := by
  rw [show D2M8K2.u7695 = KTree.node D2M8K2.t7702 (nat_lit 16262670) (nat_lit 3779996848) (nat_lit 0) D2M8K2.t7703 from rfl, allE_node, rows7702, irow7695, rows7703]
  all_goals rfl

theorem atot7695 : totK PD2M8K2 D2M8K2.u7695 = [0, 0, 86707775517, 618935681443, 817596169114, 268591364908, 18567029682, 0] := by
  rw [show D2M8K2.u7695 = KTree.node D2M8K2.t7702 (nat_lit 16262670) (nat_lit 3779996848) (nat_lit 0) D2M8K2.t7703 from rfl, totK_node, tot7702, tot7703]
  decide +kernel

theorem arows7698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7698 = true := by
  rw [show D2M8K2.u7698 = KTree.node D2M8K2.t7704 (nat_lit 16264084) (nat_lit 3685469850) (nat_lit 0) D2M8K2.t7705 from rfl, allE_node, rows7704, irow7698, rows7705]
  all_goals rfl

theorem atot7698 : totK PD2M8K2 D2M8K2.u7698 = [0, 0, 269259731350, 732052647171, 640609277595, 174334297784, 5521894595, 0] := by
  rw [show D2M8K2.u7698 = KTree.node D2M8K2.t7704 (nat_lit 16264084) (nat_lit 3685469850) (nat_lit 0) D2M8K2.t7705 from rfl, totK_node, tot7704, tot7705]
  decide +kernel

theorem arows7699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7699 = true := by
  rw [show D2M8K2.u7699 = KTree.node D2M8K2.t7706 (nat_lit 16265553) (nat_lit 1285281295) (nat_lit 0) D2M8K2.t7707 from rfl, allE_node, rows7706, irow7699, rows7707]
  all_goals rfl

theorem atot7699 : totK PD2M8K2 D2M8K2.u7699 = [0, 0, 175934456340, 757639235611, 755515637453, 122244654944, 1164319620, 0] := by
  rw [show D2M8K2.u7699 = KTree.node D2M8K2.t7706 (nat_lit 16265553) (nat_lit 1285281295) (nat_lit 0) D2M8K2.t7707 from rfl, totK_node, tot7706, tot7707]
  decide +kernel

theorem arows7701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7701 = true := by
  rw [show D2M8K2.u7701 = KTree.node D2M8K2.t7708 (nat_lit 16267237) (nat_lit 1357964992) (nat_lit 0) D2M8K2.t7709 from rfl, allE_node, rows7708, irow7701, rows7709]
  all_goals rfl

theorem atot7701 : totK PD2M8K2 D2M8K2.u7701 = [0, 0, 177978768650, 647642062223, 729883006853, 210341336004, 11885407614, 0] := by
  rw [show D2M8K2.u7701 = KTree.node D2M8K2.t7708 (nat_lit 16267237) (nat_lit 1357964992) (nat_lit 0) D2M8K2.t7709 from rfl, totK_node, tot7708, tot7709]
  decide +kernel

theorem arows7702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7702 = true := by
  rw [show D2M8K2.u7702 = KTree.node D2M8K2.t7710 (nat_lit 16272070) (nat_lit 2989447290) (nat_lit 0) D2M8K2.t7711 from rfl, allE_node, rows7710, irow7702, rows7711]
  all_goals rfl

theorem atot7702 : totK PD2M8K2 D2M8K2.u7702 = [0, 0, 238721128688, 802301939490, 637977301235, 86546372409, 1062926506, 0] := by
  rw [show D2M8K2.u7702 = KTree.node D2M8K2.t7710 (nat_lit 16272070) (nat_lit 2989447290) (nat_lit 0) D2M8K2.t7711 from rfl, totK_node, tot7710, tot7711]
  decide +kernel

theorem arows7707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7707 = true := by
  rw [show D2M8K2.u7707 = KTree.node D2M8K2.t7712 (nat_lit 16274385) (nat_lit 1435823754) (nat_lit 0) D2M8K2.t7713 from rfl, allE_node, rows7712, irow7707, rows7713]
  all_goals rfl

theorem atot7707 : totK PD2M8K2 D2M8K2.u7707 = [0, 0, 227018233444, 744818755622, 689854989448, 128821937079, 3783381897, 0] := by
  rw [show D2M8K2.u7707 = KTree.node D2M8K2.t7712 (nat_lit 16274385) (nat_lit 1435823754) (nat_lit 0) D2M8K2.t7713 from rfl, totK_node, tot7712, tot7713]
  decide +kernel

theorem arows7708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7708 = true := by
  rw [show D2M8K2.u7708 = KTree.node D2M8K2.t7714 (nat_lit 16275922) (nat_lit 4072409954) (nat_lit 0) D2M8K2.t7715 from rfl, allE_node, rows7714, irow7708, rows7715]
  all_goals rfl

theorem atot7708 : totK PD2M8K2 D2M8K2.u7708 = [0, 0, 193564049060, 763102396688, 721814417129, 117770159736, 1240621948, 0] := by
  rw [show D2M8K2.u7708 = KTree.node D2M8K2.t7714 (nat_lit 16275922) (nat_lit 4072409954) (nat_lit 0) D2M8K2.t7715 from rfl, totK_node, tot7714, tot7715]
  decide +kernel

theorem arows7710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7710 = true := by
  rw [show D2M8K2.u7710 = KTree.node D2M8K2.t7716 (nat_lit 16277772) (nat_lit 3608248717) (nat_lit 0) D2M8K2.t7717 from rfl, allE_node, rows7716, irow7710, rows7717]
  all_goals rfl

theorem atot7710 : totK PD2M8K2 D2M8K2.u7710 = [0, 0, 0, 406976327946, 952372904104, 389299430216, 22329958799, 0] := by
  rw [show D2M8K2.u7710 = KTree.node D2M8K2.t7716 (nat_lit 16277772) (nat_lit 3608248717) (nat_lit 0) D2M8K2.t7717 from rfl, totK_node, tot7716, tot7717]
  decide +kernel

theorem arows7711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7711 = true := by
  rw [show D2M8K2.u7711 = KTree.node D2M8K2.t7718 (nat_lit 16279379) (nat_lit 2157982827) (nat_lit 0) D2M8K2.t7719 from rfl, allE_node, rows7718, irow7711, rows7719]
  all_goals rfl

theorem atot7711 : totK PD2M8K2 D2M8K2.u7711 = [0, 0, 0, 194873458169, 774427357257, 618748505396, 90936783940, 1206465782] := by
  rw [show D2M8K2.u7711 = KTree.node D2M8K2.t7718 (nat_lit 16279379) (nat_lit 2157982827) (nat_lit 0) D2M8K2.t7719 from rfl, totK_node, tot7718, tot7719]
  decide +kernel

theorem arows7714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7714 = true := by
  rw [show D2M8K2.u7714 = KTree.node D2M8K2.t7720 (nat_lit 16281825) (nat_lit 1816062054) (nat_lit 0) D2M8K2.t7721 from rfl, allE_node, rows7720, irow7714, rows7721]
  all_goals rfl

theorem atot7714 : totK PD2M8K2 D2M8K2.u7714 = [0, 0, 0, 333805243870, 903017586785, 511992671293, 39724231376, 0] := by
  rw [show D2M8K2.u7714 = KTree.node D2M8K2.t7720 (nat_lit 16281825) (nat_lit 1816062054) (nat_lit 0) D2M8K2.t7721 from rfl, totK_node, tot7720, tot7721]
  decide +kernel

theorem arows7715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7715 = true := by
  rw [show D2M8K2.u7715 = KTree.node D2M8K2.t7722 (nat_lit 16285041) (nat_lit 1431865371) (nat_lit 0) D2M8K2.t7723 from rfl, allE_node, rows7722, irow7715, rows7723]
  all_goals rfl

theorem atot7715 : totK PD2M8K2 D2M8K2.u7715 = [0, 0, 0, 391768746634, 950068106233, 438181040490, 29946387533, 0] := by
  rw [show D2M8K2.u7715 = KTree.node D2M8K2.t7722 (nat_lit 16285041) (nat_lit 1431865371) (nat_lit 0) D2M8K2.t7723 from rfl, totK_node, tot7722, tot7723]
  decide +kernel

theorem arows7717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7717 = true := by
  rw [show D2M8K2.u7717 = KTree.node D2M8K2.t7724 (nat_lit 16286517) (nat_lit 1546560152) (nat_lit 0) D2M8K2.t7725 from rfl, allE_node, rows7724, irow7717, rows7725]
  all_goals rfl

theorem atot7717 : totK PD2M8K2 D2M8K2.u7717 = [0, 0, 0, 126525245439, 661364417819, 757063398866, 196134931888, 9579374723] := by
  rw [show D2M8K2.u7717 = KTree.node D2M8K2.t7724 (nat_lit 16286517) (nat_lit 1546560152) (nat_lit 0) D2M8K2.t7725 from rfl, totK_node, tot7724, tot7725]
  decide +kernel

theorem arows7718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7718 = true := by
  rw [show D2M8K2.u7718 = KTree.node D2M8K2.t7726 (nat_lit 16291829) (nat_lit 2197073260) (nat_lit 0) D2M8K2.t7727 from rfl, allE_node, rows7726, irow7718, rows7727]
  all_goals rfl

theorem atot7718 : totK PD2M8K2 D2M8K2.u7718 = [0, 0, 0, 262858634678, 789251249925, 574778065021, 105958838148, 3436822651] := by
  rw [show D2M8K2.u7718 = KTree.node D2M8K2.t7726 (nat_lit 16291829) (nat_lit 2197073260) (nat_lit 0) D2M8K2.t7727 from rfl, totK_node, tot7726, tot7727]
  decide +kernel

theorem arows7722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7722 = true := by
  rw [show D2M8K2.u7722 = KTree.node D2M8K2.t7728 (nat_lit 16293422) (nat_lit 2648132449) (nat_lit 0) D2M8K2.t7729 from rfl, allE_node, rows7728, irow7722, rows7729]
  all_goals rfl

theorem atot7722 : totK PD2M8K2 D2M8K2.u7722 = [0, 0, 0, 148952904728, 746268219118, 678066420788, 94370982292, 1021600638] := by
  rw [show D2M8K2.u7722 = KTree.node D2M8K2.t7728 (nat_lit 16293422) (nat_lit 2648132449) (nat_lit 0) D2M8K2.t7729 from rfl, totK_node, tot7728, tot7729]
  decide +kernel

theorem arows7723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7723 = true := by
  rw [show D2M8K2.u7723 = KTree.node D2M8K2.t7730 (nat_lit 16295524) (nat_lit 4003814300) (nat_lit 0) D2M8K2.t7731 from rfl, allE_node, rows7730, irow7723, rows7731]
  all_goals rfl

theorem atot7723 : totK PD2M8K2 D2M8K2.u7723 = [0, 0, 0, 404755993292, 864346143384, 420672487082, 74807915670, 3552795014] := by
  rw [show D2M8K2.u7723 = KTree.node D2M8K2.t7730 (nat_lit 16295524) (nat_lit 4003814300) (nat_lit 0) D2M8K2.t7731 from rfl, totK_node, tot7730, tot7731]
  decide +kernel

theorem arows7725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7725 = true := by
  rw [show D2M8K2.u7725 = KTree.node D2M8K2.t7732 (nat_lit 16340697) (nat_lit 1731128826) (nat_lit 0) D2M8K2.t7733 from rfl, allE_node, rows7732, irow7725, rows7733]
  all_goals rfl

theorem atot7725 : totK PD2M8K2 D2M8K2.u7725 = [0, 0, 338222535339, 843341407035, 463099487834, 112021671256, 8935385149, 0] := by
  rw [show D2M8K2.u7725 = KTree.node D2M8K2.t7732 (nat_lit 16340697) (nat_lit 1731128826) (nat_lit 0) D2M8K2.t7733 from rfl, totK_node, tot7732, tot7733]
  decide +kernel

theorem arows7726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7726 = true := by
  rw [show D2M8K2.u7726 = KTree.node D2M8K2.t7734 (nat_lit 16342332) (nat_lit 3224907551) (nat_lit 0) D2M8K2.t7735 from rfl, allE_node, rows7734, irow7726, rows7735]
  all_goals rfl

theorem atot7726 : totK PD2M8K2 D2M8K2.u7726 = [0, 0, 133495785896, 678968456149, 818596526137, 123469592106, 1310166938, 0] := by
  rw [show D2M8K2.u7726 = KTree.node D2M8K2.t7734 (nat_lit 16342332) (nat_lit 3224907551) (nat_lit 0) D2M8K2.t7735 from rfl, totK_node, tot7734, tot7735]
  decide +kernel

theorem arows7729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7729 = true := by
  rw [show D2M8K2.u7729 = KTree.node D2M8K2.t7736 (nat_lit 16344387) (nat_lit 3663281937) (nat_lit 0) D2M8K2.t7737 from rfl, allE_node, rows7736, irow7729, rows7737]
  all_goals rfl

theorem atot7729 : totK PD2M8K2 D2M8K2.u7729 = [0, 0, 348450944218, 947353918375, 504887622998, 35075005595, 0, 0] := by
  rw [show D2M8K2.u7729 = KTree.node D2M8K2.t7736 (nat_lit 16344387) (nat_lit 3663281937) (nat_lit 0) D2M8K2.t7737 from rfl, totK_node, tot7736, tot7737]
  decide +kernel

theorem arows7730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7730 = true := by
  rw [show D2M8K2.u7730 = KTree.node D2M8K2.t7738 (nat_lit 16346050) (nat_lit 3792237307) (nat_lit 0) D2M8K2.t7739 from rfl, allE_node, rows7738, irow7730, rows7739]
  all_goals rfl

theorem atot7730 : totK PD2M8K2 D2M8K2.u7730 = [0, 0, 84126500797, 543204657478, 863050344427, 303567114138, 15013989272, 0] := by
  rw [show D2M8K2.u7730 = KTree.node D2M8K2.t7738 (nat_lit 16346050) (nat_lit 3792237307) (nat_lit 0) D2M8K2.t7739 from rfl, totK_node, tot7738, tot7739]
  decide +kernel

theorem arows7732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7732 = true := by
  rw [show D2M8K2.u7732 = KTree.node D2M8K2.t7740 (nat_lit 16347611) (nat_lit 2322489828) (nat_lit 0) D2M8K2.t7741 from rfl, allE_node, rows7740, irow7732, rows7741]
  all_goals rfl

theorem atot7732 : totK PD2M8K2 D2M8K2.u7732 = [0, 0, 339452968416, 926162350033, 511397794162, 35934675359, 0, 0] := by
  rw [show D2M8K2.u7732 = KTree.node D2M8K2.t7740 (nat_lit 16347611) (nat_lit 2322489828) (nat_lit 0) D2M8K2.t7741 from rfl, totK_node, tot7740, tot7741]
  decide +kernel

theorem arows7733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7733 = true := by
  rw [show D2M8K2.u7733 = KTree.node D2M8K2.t7742 (nat_lit 16349322) (nat_lit 2244487559) (nat_lit 0) D2M8K2.t7743 from rfl, allE_node, rows7742, irow7733, rows7743]
  all_goals rfl

theorem atot7733 : totK PD2M8K2 D2M8K2.u7733 = [0, 0, 45589247412, 492559865189, 926304908540, 287547529658, 13049727234, 0] := by
  rw [show D2M8K2.u7733 = KTree.node D2M8K2.t7742 (nat_lit 16349322) (nat_lit 2244487559) (nat_lit 0) D2M8K2.t7743 from rfl, totK_node, tot7742, tot7743]
  decide +kernel

theorem arows7739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7739 = true := by
  rw [show D2M8K2.u7739 = KTree.node D2M8K2.t7744 (nat_lit 16351378) (nat_lit 3040042244) (nat_lit 32) D2M8K2.t7745 from rfl, allE_node, rows7744, irow7739, rows7745]
  all_goals rfl

theorem atot7739 : totK PD2M8K2 D2M8K2.u7739 = [0, 0, 273827933997, 867707962337, 561985171638, 60104698451, 1104198603, 0] := by
  rw [show D2M8K2.u7739 = KTree.node D2M8K2.t7744 (nat_lit 16351378) (nat_lit 3040042244) (nat_lit 32) D2M8K2.t7745 from rfl, totK_node, tot7744, tot7745]
  decide +kernel

theorem arows7740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7740 = true := by
  rw [show D2M8K2.u7740 = KTree.node D2M8K2.t7746 (nat_lit 16353954) (nat_lit 2725426548) (nat_lit 0) D2M8K2.t7747 from rfl, allE_node, rows7746, irow7740, rows7747]
  all_goals rfl

theorem atot7740 : totK PD2M8K2 D2M8K2.u7740 = [0, 0, 261833279947, 817667309539, 616814673045, 88018992066, 3581949829, 0] := by
  rw [show D2M8K2.u7740 = KTree.node D2M8K2.t7746 (nat_lit 16353954) (nat_lit 2725426548) (nat_lit 0) D2M8K2.t7747 from rfl, totK_node, tot7746, tot7747]
  decide +kernel

theorem arows7742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7742 = true := by
  rw [show D2M8K2.u7742 = KTree.node D2M8K2.t7748 (nat_lit 16355166) (nat_lit 3987577423) (nat_lit 0) D2M8K2.t7749 from rfl, allE_node, rows7748, irow7742, rows7749]
  all_goals rfl

theorem atot7742 : totK PD2M8K2 D2M8K2.u7742 = [0, 0, 174985890020, 762770137786, 746121540320, 104568490898, 1096505104, 0] := by
  rw [show D2M8K2.u7742 = KTree.node D2M8K2.t7748 (nat_lit 16355166) (nat_lit 3987577423) (nat_lit 0) D2M8K2.t7749 from rfl, totK_node, tot7748, tot7749]
  decide +kernel

theorem arows7743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7743 = true := by
  rw [show D2M8K2.u7743 = KTree.node D2M8K2.t7750 (nat_lit 16360868) (nat_lit 2777369328) (nat_lit 0) D2M8K2.t7751 from rfl, allE_node, rows7750, irow7743, rows7751]
  all_goals rfl

theorem atot7743 : totK PD2M8K2 D2M8K2.u7743 = [0, 0, 0, 425795628683, 959123790128, 320441244402, 14718187971, 0] := by
  rw [show D2M8K2.u7743 = KTree.node D2M8K2.t7750 (nat_lit 16360868) (nat_lit 2777369328) (nat_lit 0) D2M8K2.t7751 from rfl, totK_node, tot7750, tot7751]
  decide +kernel

theorem arows7746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7746 = true := by
  rw [show D2M8K2.u7746 = KTree.node D2M8K2.t7752 (nat_lit 16362577) (nat_lit 1543709230) (nat_lit 0) D2M8K2.t7753 from rfl, allE_node, rows7752, irow7746, rows7753]
  all_goals rfl

theorem atot7746 : totK PD2M8K2 D2M8K2.u7746 = [0, 0, 0, 172174710085, 796028242660, 639070168377, 73537720810, 1103454931] := by
  rw [show D2M8K2.u7746 = KTree.node D2M8K2.t7752 (nat_lit 16362577) (nat_lit 1543709230) (nat_lit 0) D2M8K2.t7753 from rfl, totK_node, tot7752, tot7753]
  decide +kernel

theorem arows7747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7747 = true := by
  rw [show D2M8K2.u7747 = KTree.node D2M8K2.t7754 (nat_lit 16365320) (nat_lit 3701213405) (nat_lit 0) D2M8K2.t7755 from rfl, allE_node, rows7754, irow7747, rows7755]
  all_goals rfl

theorem atot7747 : totK PD2M8K2 D2M8K2.u7747 = [0, 0, 0, 452979797282, 955243438543, 355453562491, 16951060829, 0] := by
  rw [show D2M8K2.u7747 = KTree.node D2M8K2.t7754 (nat_lit 16365320) (nat_lit 3701213405) (nat_lit 0) D2M8K2.t7755 from rfl, totK_node, tot7754, tot7755]
  decide +kernel

theorem arows7749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7749 = true := by
  rw [show D2M8K2.u7749 = KTree.node D2M8K2.t7756 (nat_lit 16368777) (nat_lit 1850716406) (nat_lit 0) D2M8K2.t7757 from rfl, allE_node, rows7756, irow7749, rows7757]
  all_goals rfl

theorem atot7749 : totK PD2M8K2 D2M8K2.u7749 = [0, 0, 0, 398973351847, 936704873588, 412443435950, 25747153916, 0] := by
  rw [show D2M8K2.u7749 = KTree.node D2M8K2.t7756 (nat_lit 16368777) (nat_lit 1850716406) (nat_lit 0) D2M8K2.t7757 from rfl, totK_node, tot7756, tot7757]
  decide +kernel

theorem arows7750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7750 = true := by
  rw [show D2M8K2.u7750 = KTree.node D2M8K2.t7758 (nat_lit 16374537) (nat_lit 1838833587) (nat_lit 0) D2M8K2.t7759 from rfl, allE_node, rows7758, irow7750, rows7759]
  all_goals rfl

theorem atot7750 : totK PD2M8K2 D2M8K2.u7750 = [0, 0, 0, 468301501318, 934321163846, 306210212086, 15835754105, 0] := by
  rw [show D2M8K2.u7750 = KTree.node D2M8K2.t7758 (nat_lit 16374537) (nat_lit 1838833587) (nat_lit 0) D2M8K2.t7759 from rfl, totK_node, tot7758, tot7759]
  decide +kernel

theorem arows7754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7754 = true := by
  rw [show D2M8K2.u7754 = KTree.node D2M8K2.t7760 (nat_lit 16375788) (nat_lit 3185297290) (nat_lit 0) D2M8K2.t7761 from rfl, allE_node, rows7760, irow7754, rows7761]
  all_goals rfl

theorem atot7754 : totK PD2M8K2 D2M8K2.u7754 = [0, 0, 0, 200178935900, 798146406455, 601424508498, 82175835660, 1061529118] := by
  rw [show D2M8K2.u7754 = KTree.node D2M8K2.t7760 (nat_lit 16375788) (nat_lit 3185297290) (nat_lit 0) D2M8K2.t7761 from rfl, totK_node, tot7760, tot7761]
  decide +kernel

theorem arows7755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7755 = true := by
  rw [show D2M8K2.u7755 = KTree.node D2M8K2.t7762 (nat_lit 16381640) (nat_lit 3528655208) (nat_lit 0) D2M8K2.t7763 from rfl, allE_node, rows7762, irow7755, rows7763]
  all_goals rfl

theorem atot7755 : totK PD2M8K2 D2M8K2.u7755 = [0, 0, 269505428543, 650128060929, 439041482122, 291280287129, 80533501329, 3718133097] := by
  rw [show D2M8K2.u7755 = KTree.node D2M8K2.t7762 (nat_lit 16381640) (nat_lit 3528655208) (nat_lit 0) D2M8K2.t7763 from rfl, totK_node, tot7762, tot7763]
  decide +kernel

theorem arows7757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7757 = true := by
  rw [show D2M8K2.u7757 = KTree.node D2M8K2.t7764 (nat_lit 16383269) (nat_lit 2267483530) (nat_lit 0) D2M8K2.t7765 from rfl, allE_node, rows7764, irow7757, rows7765]
  all_goals rfl

theorem atot7757 : totK PD2M8K2 D2M8K2.u7757 = [0, 0, 137060727193, 723228478114, 784862530928, 116314557429, 1369150432, 0] := by
  rw [show D2M8K2.u7757 = KTree.node D2M8K2.t7764 (nat_lit 16383269) (nat_lit 2267483530) (nat_lit 0) D2M8K2.t7765 from rfl, totK_node, tot7764, tot7765]
  decide +kernel

theorem arows7758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7758 = true := by
  rw [show D2M8K2.u7758 = KTree.node D2M8K2.t7766 (nat_lit 16385624) (nat_lit 2690884642) (nat_lit 0) D2M8K2.t7767 from rfl, allE_node, rows7766, irow7758, rows7767]
  all_goals rfl

theorem atot7758 : totK PD2M8K2 D2M8K2.u7758 = [0, 0, 372881022902, 926221285329, 509907058110, 42200536561, 0, 0] := by
  rw [show D2M8K2.u7758 = KTree.node D2M8K2.t7766 (nat_lit 16385624) (nat_lit 2690884642) (nat_lit 0) D2M8K2.t7767 from rfl, totK_node, tot7766, tot7767]
  decide +kernel

theorem arows7761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7761 = true := by
  rw [show D2M8K2.u7761 = KTree.node D2M8K2.t7768 (nat_lit 16387261) (nat_lit 1188156559) (nat_lit 0) D2M8K2.t7769 from rfl, allE_node, rows7768, irow7761, rows7769]
  all_goals rfl

theorem atot7761 : totK PD2M8K2 D2M8K2.u7761 = [0, 0, 41466562539, 581839033697, 917644130876, 282854816614, 13250672716, 0] := by
  rw [show D2M8K2.u7761 = KTree.node D2M8K2.t7768 (nat_lit 16387261) (nat_lit 1188156559) (nat_lit 0) D2M8K2.t7769 from rfl, totK_node, tot7768, tot7769]
  decide +kernel

theorem arows7762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7762 = true := by
  rw [show D2M8K2.u7762 = KTree.node D2M8K2.t7770 (nat_lit 16388906) (nat_lit 4105264466) (nat_lit 0) D2M8K2.t7771 from rfl, allE_node, rows7770, irow7762, rows7771]
  all_goals rfl

theorem atot7762 : totK PD2M8K2 D2M8K2.u7762 = [0, 0, 364065557223, 886523013535, 477124469344, 66047099002, 3060566153, 0] := by
  rw [show D2M8K2.u7762 = KTree.node D2M8K2.t7770 (nat_lit 16388906) (nat_lit 4105264466) (nat_lit 0) D2M8K2.t7771 from rfl, totK_node, tot7770, tot7771]
  decide +kernel

theorem arows7764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7764 = true := by
  rw [show D2M8K2.u7764 = KTree.node D2M8K2.t7772 (nat_lit 16390467) (nat_lit 3691899134) (nat_lit 0) D2M8K2.t7773 from rfl, allE_node, rows7772, irow7764, rows7773]
  all_goals rfl

theorem atot7764 : totK PD2M8K2 D2M8K2.u7764 = [0, 0, 60425529563, 609779461137, 927397022237, 212370358038, 7165314891, 0] := by
  rw [show D2M8K2.u7764 = KTree.node D2M8K2.t7772 (nat_lit 16390467) (nat_lit 3691899134) (nat_lit 0) D2M8K2.t7773 from rfl, totK_node, tot7772, tot7773]
  decide +kernel

theorem arows7765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7765 = true := by
  rw [show D2M8K2.u7765 = KTree.node D2M8K2.t7774 (nat_lit 16392710) (nat_lit 4137174129) (nat_lit 0) D2M8K2.t7775 from rfl, allE_node, rows7774, irow7765, rows7775]
  all_goals rfl

theorem atot7765 : totK PD2M8K2 D2M8K2.u7765 = [0, 0, 411199153329, 942712585575, 444385764617, 41564970731, 0, 0] := by
  rw [show D2M8K2.u7765 = KTree.node D2M8K2.t7774 (nat_lit 16392710) (nat_lit 4137174129) (nat_lit 0) D2M8K2.t7775 from rfl, totK_node, tot7774, tot7775]
  decide +kernel

theorem arows7770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7770 = true := by
  rw [show D2M8K2.u7770 = KTree.node D2M8K2.t7776 (nat_lit 16399505) (nat_lit 2210428727) (nat_lit 0) D2M8K2.t7777 from rfl, allE_node, rows7776, irow7770, rows7777]
  all_goals rfl

theorem atot7770 : totK PD2M8K2 D2M8K2.u7770 = [0, 0, 354538315953, 928566286547, 517891094993, 39566768713, 0, 0] := by
  rw [show D2M8K2.u7770 = KTree.node D2M8K2.t7776 (nat_lit 16399505) (nat_lit 2210428727) (nat_lit 0) D2M8K2.t7777 from rfl, totK_node, tot7776, tot7777]
  decide +kernel

theorem arows7771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7771 = true := by
  rw [show D2M8K2.u7771 = KTree.node D2M8K2.t7778 (nat_lit 16401172) (nat_lit 3691847987) (nat_lit 0) D2M8K2.t7779 from rfl, allE_node, rows7778, irow7771, rows7779]
  all_goals rfl

theorem atot7771 : totK PD2M8K2 D2M8K2.u7771 = [0, 55649345463, 68083696581, 457219272035, 914782227915, 292836634536, 13949453364, 0] := by
  rw [show D2M8K2.u7771 = KTree.node D2M8K2.t7778 (nat_lit 16401172) (nat_lit 3691847987) (nat_lit 0) D2M8K2.t7779 from rfl, totK_node, tot7778, tot7779]
  decide +kernel

theorem arows7773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7773 = true := by
  rw [show D2M8K2.u7773 = KTree.node D2M8K2.t7780 (nat_lit 16921560) (nat_lit 3561687974) (nat_lit 0) D2M8K2.t7781 from rfl, allE_node, rows7780, irow7773, rows7781]
  all_goals rfl

theorem atot7773 : totK PD2M8K2 D2M8K2.u7773 = [0, 377292247003, 956764076172, 434086510086, 22386190152, 0, 0, 0] := by
  rw [show D2M8K2.u7773 = KTree.node D2M8K2.t7780 (nat_lit 16921560) (nat_lit 3561687974) (nat_lit 0) D2M8K2.t7781 from rfl, totK_node, tot7780, tot7781]
  decide +kernel

theorem arows7774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7774 = true := by
  rw [show D2M8K2.u7774 = KTree.node D2M8K2.t7782 (nat_lit 16923212) (nat_lit 3160196716) (nat_lit 0) D2M8K2.t7783 from rfl, allE_node, rows7782, irow7774, rows7783]
  all_goals rfl

theorem atot7774 : totK PD2M8K2 D2M8K2.u7774 = [0, 87164153352, 653790725160, 895327063151, 156581129966, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7774 = KTree.node D2M8K2.t7782 (nat_lit 16923212) (nat_lit 3160196716) (nat_lit 0) D2M8K2.t7783 from rfl, totK_node, tot7782, tot7783]
  decide +kernel

theorem arows7777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7777 = true := by
  rw [show D2M8K2.u7777 = KTree.node D2M8K2.t7784 (nat_lit 16928324) (nat_lit 3275731804) (nat_lit 0) D2M8K2.t7785 from rfl, allE_node, rows7784, irow7777, rows7785]
  all_goals rfl

theorem atot7777 : totK PD2M8K2 D2M8K2.u7777 = [0, 326295402710, 913554142314, 523851112283, 43070855011, 0, 0, 0] := by
  rw [show D2M8K2.u7777 = KTree.node D2M8K2.t7784 (nat_lit 16928324) (nat_lit 3275731804) (nat_lit 0) D2M8K2.t7785 from rfl, totK_node, tot7784, tot7785]
  decide +kernel

theorem arows7778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7778 = true := by
  rw [show D2M8K2.u7778 = KTree.node D2M8K2.t7786 (nat_lit 16930035) (nat_lit 2312504568) (nat_lit 0) D2M8K2.t7787 from rfl, allE_node, rows7786, irow7778, rows7787]
  all_goals rfl

theorem atot7778 : totK PD2M8K2 D2M8K2.u7778 = [0, 86311067613, 515697251222, 874172357151, 283778799460, 13049727234, 0, 0] := by
  rw [show D2M8K2.u7778 = KTree.node D2M8K2.t7786 (nat_lit 16930035) (nat_lit 2312504568) (nat_lit 0) D2M8K2.t7787 from rfl, totK_node, tot7786, tot7787]
  decide +kernel

theorem arows7780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7780 = true := by
  rw [show D2M8K2.u7780 = KTree.node D2M8K2.t7788 (nat_lit 16932082) (nat_lit 4109470449) (nat_lit 0) D2M8K2.t7789 from rfl, allE_node, rows7788, irow7780, rows7789]
  all_goals rfl

theorem atot7780 : totK PD2M8K2 D2M8K2.u7780 = [0, 293664900667, 904043483209, 557538641705, 40863142696, 0, 0, 0] := by
  rw [show D2M8K2.u7780 = KTree.node D2M8K2.t7788 (nat_lit 16932082) (nat_lit 4109470449) (nat_lit 0) D2M8K2.t7789 from rfl, totK_node, tot7788, tot7789]
  decide +kernel

theorem arows7781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7781 = true := by
  rw [show D2M8K2.u7781 = KTree.node D2M8K2.t7790 (nat_lit 16933870) (nat_lit 1814617927) (nat_lit 0) D2M8K2.t7791 from rfl, allE_node, rows7790, irow7781, rows7791]
  all_goals rfl

theorem atot7781 : totK PD2M8K2 D2M8K2.u7781 = [0, 106674435337, 553530460642, 828469209374, 261572064033, 13250685261, 0, 0] := by
  rw [show D2M8K2.u7781 = KTree.node D2M8K2.t7790 (nat_lit 16933870) (nat_lit 1814617927) (nat_lit 0) D2M8K2.t7791 from rfl, totK_node, tot7790, tot7791]
  decide +kernel

theorem arows7785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7785 = true := by
  rw [show D2M8K2.u7785 = KTree.node D2M8K2.t7792 (nat_lit 16935337) (nat_lit 1496149245) (nat_lit 0) D2M8K2.t7793 from rfl, allE_node, rows7792, irow7785, rows7793]
  all_goals rfl

theorem atot7785 : totK PD2M8K2 D2M8K2.u7785 = [0, 314368383975, 885184679584, 536819167878, 49624531948, 0, 0, 0] := by
  rw [show D2M8K2.u7785 = KTree.node D2M8K2.t7792 (nat_lit 16935337) (nat_lit 1496149245) (nat_lit 0) D2M8K2.t7793 from rfl, totK_node, tot7792, tot7793]
  decide +kernel

theorem arows7786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7786 = true := by
  rw [show D2M8K2.u7786 = KTree.node D2M8K2.t7794 (nat_lit 16937289) (nat_lit 1858190061) (nat_lit 0) D2M8K2.t7795 from rfl, allE_node, rows7794, irow7786, rows7795]
  all_goals rfl

theorem atot7786 : totK PD2M8K2 D2M8K2.u7786 = [0, 138155694125, 642017508088, 818445972342, 190783582333, 4980514959, 0, 0] := by
  rw [show D2M8K2.u7786 = KTree.node D2M8K2.t7794 (nat_lit 16937289) (nat_lit 1858190061) (nat_lit 0) D2M8K2.t7795 from rfl, totK_node, tot7794, tot7795]
  decide +kernel

theorem arows7788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7788 = true := by
  rw [show D2M8K2.u7788 = KTree.node D2M8K2.t7796 (nat_lit 16939468) (nat_lit 3733966991) (nat_lit 0) D2M8K2.t7797 from rfl, allE_node, rows7796, irow7788, rows7797]
  all_goals rfl

theorem atot7788 : totK PD2M8K2 D2M8K2.u7788 = [0, 188279367166, 720109443709, 703582505496, 167284436361, 4967996017, 0, 0] := by
  rw [show D2M8K2.u7788 = KTree.node D2M8K2.t7796 (nat_lit 16939468) (nat_lit 3733966991) (nat_lit 0) D2M8K2.t7797 from rfl, totK_node, tot7796, tot7797]
  decide +kernel

theorem arows7789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7789 = true := by
  rw [show D2M8K2.u7789 = KTree.node D2M8K2.t7798 (nat_lit 16941468) (nat_lit 3511600203) (nat_lit 0) D2M8K2.t7799 from rfl, allE_node, rows7798, irow7789, rows7799]
  all_goals rfl

theorem atot7789 : totK PD2M8K2 D2M8K2.u7789 = [0, 0, 417006695314, 958690047744, 377916178366, 19778478255, 0, 0] := by
  rw [show D2M8K2.u7789 = KTree.node D2M8K2.t7798 (nat_lit 16941468) (nat_lit 3511600203) (nat_lit 0) D2M8K2.t7799 from rfl, totK_node, tot7798, tot7799]
  decide +kernel

theorem arows7792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7792 = true := by
  rw [show D2M8K2.u7792 = KTree.node D2M8K2.t7800 (nat_lit 16943027) (nat_lit 2974473560) (nat_lit 0) D2M8K2.t7801 from rfl, allE_node, rows7800, irow7792, rows7801]
  all_goals rfl

theorem atot7792 : totK PD2M8K2 D2M8K2.u7792 = [0, 0, 168653805842, 754794736620, 683355344007, 111552547013, 1369150432, 0] := by
  rw [show D2M8K2.u7792 = KTree.node D2M8K2.t7800 (nat_lit 16943027) (nat_lit 2974473560) (nat_lit 0) D2M8K2.t7801 from rfl, totK_node, tot7800, tot7801]
  decide +kernel

theorem arows7793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7793 = true := by
  rw [show D2M8K2.u7793 = KTree.node D2M8K2.t7802 (nat_lit 16948655) (nat_lit 2392818748) (nat_lit 128) D2M8K2.t7803 from rfl, allE_node, rows7802, irow7793, rows7803]
  all_goals rfl

theorem atot7793 : totK PD2M8K2 D2M8K2.u7793 = [0, 0, 333468099103, 906956826580, 494284877328, 36407332192, 0, 0] := by
  rw [show D2M8K2.u7793 = KTree.node D2M8K2.t7802 (nat_lit 16948655) (nat_lit 2392818748) (nat_lit 128) D2M8K2.t7803 from rfl, totK_node, tot7802, tot7803]
  decide +kernel

theorem arows7795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7795 = true := by
  rw [show D2M8K2.u7795 = KTree.node D2M8K2.t7804 (nat_lit 16951955) (nat_lit 2880029674) (nat_lit 0) D2M8K2.t7805 from rfl, allE_node, rows7804, irow7795, rows7805]
  all_goals rfl

theorem atot7795 : totK PD2M8K2 D2M8K2.u7795 = [0, 0, 378162363667, 939449779474, 422929490038, 22698107825, 0, 0] := by
  rw [show D2M8K2.u7795 = KTree.node D2M8K2.t7804 (nat_lit 16951955) (nat_lit 2880029674) (nat_lit 0) D2M8K2.t7805 from rfl, totK_node, tot7804, tot7805]
  decide +kernel

theorem arows7796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7796 = true := by
  rw [show D2M8K2.u7796 = KTree.node D2M8K2.t7806 (nat_lit 16955451) (nat_lit 3775879737) (nat_lit 0) D2M8K2.t7807 from rfl, allE_node, rows7806, irow7796, rows7807]
  all_goals rfl

theorem atot7796 : totK PD2M8K2 D2M8K2.u7796 = [0, 0, 377805981580, 965424352205, 411733653667, 16122303122, 0, 0] := by
  rw [show D2M8K2.u7796 = KTree.node D2M8K2.t7806 (nat_lit 16955451) (nat_lit 3775879737) (nat_lit 0) D2M8K2.t7807 from rfl, totK_node, tot7806, tot7807]
  decide +kernel

theorem arows7803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7803 = true := by
  rw [show D2M8K2.u7803 = KTree.node D2M8K2.t7808 (nat_lit 16958706) (nat_lit 3147183120) (nat_lit 0) D2M8K2.t7809 from rfl, allE_node, rows7808, irow7803, rows7809]
  all_goals rfl

theorem atot7803 : totK PD2M8K2 D2M8K2.u7803 = [0, 0, 360280104552, 961502969372, 424542913556, 18812526765, 0, 0] := by
  rw [show D2M8K2.u7803 = KTree.node D2M8K2.t7808 (nat_lit 16958706) (nat_lit 3147183120) (nat_lit 0) D2M8K2.t7809 from rfl, totK_node, tot7808, tot7809]
  decide +kernel

theorem arows7804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7804 = true := by
  rw [show D2M8K2.u7804 = KTree.node D2M8K2.t7810 (nat_lit 16966050) (nat_lit 3299736308) (nat_lit 0) D2M8K2.t7811 from rfl, allE_node, rows7810, irow7804, rows7811]
  all_goals rfl

theorem atot7804 : totK PD2M8K2 D2M8K2.u7804 = [0, 269133968381, 764573908394, 631322664843, 163198198708, 9054957427, 0, 0] := by
  rw [show D2M8K2.u7804 = KTree.node D2M8K2.t7810 (nat_lit 16966050) (nat_lit 3299736308) (nat_lit 0) D2M8K2.t7811 from rfl, totK_node, tot7810, tot7811]
  decide +kernel

theorem arows7806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7806 = true := by
  rw [show D2M8K2.u7806 = KTree.node D2M8K2.t7812 (nat_lit 16967559) (nat_lit 3639394546) (nat_lit 0) D2M8K2.t7813 from rfl, allE_node, rows7812, irow7806, rows7813]
  all_goals rfl

theorem atot7806 : totK PD2M8K2 D2M8K2.u7806 = [0, 173140878375, 650266436351, 704952926816, 278324571215, 25373788367, 0, 0] := by
  rw [show D2M8K2.u7806 = KTree.node D2M8K2.t7812 (nat_lit 16967559) (nat_lit 3639394546) (nat_lit 0) D2M8K2.t7813 from rfl, totK_node, tot7812, tot7813]
  decide +kernel

theorem arows7807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7807 = true := by
  rw [show D2M8K2.u7807 = KTree.node D2M8K2.t7814 (nat_lit 16968734) (nat_lit 3881137344) (nat_lit 0) D2M8K2.t7815 from rfl, allE_node, rows7814, irow7807, rows7815]
  all_goals rfl

theorem atot7807 : totK PD2M8K2 D2M8K2.u7807 = [0, 157736353808, 585267016377, 768758864110, 300175371865, 12235609738, 0, 0] := by
  rw [show D2M8K2.u7807 = KTree.node D2M8K2.t7814 (nat_lit 16968734) (nat_lit 3881137344) (nat_lit 0) D2M8K2.t7815 from rfl, totK_node, tot7814, tot7815]
  decide +kernel

theorem arows7810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7810 = true := by
  rw [show D2M8K2.u7810 = KTree.node D2M8K2.t7816 (nat_lit 16970265) (nat_lit 1824289386) (nat_lit 0) D2M8K2.t7817 from rfl, allE_node, rows7816, irow7810, rows7817]
  all_goals rfl

theorem atot7810 : totK PD2M8K2 D2M8K2.u7810 = [0, 258439022077, 819342201352, 635140691369, 94651416747, 1163840124, 0, 0] := by
  rw [show D2M8K2.u7810 = KTree.node D2M8K2.t7816 (nat_lit 16970265) (nat_lit 1824289386) (nat_lit 0) D2M8K2.t7817 from rfl, totK_node, tot7816, tot7817]
  decide +kernel

theorem arows7811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7811 = true := by
  rw [show D2M8K2.u7811 = KTree.node D2M8K2.t7818 (nat_lit 16971990) (nat_lit 2286638863) (nat_lit 0) D2M8K2.t7819 from rfl, allE_node, rows7818, irow7811, rows7819]
  all_goals rfl

theorem atot7811 : totK PD2M8K2 D2M8K2.u7811 = [0, 141706202556, 621843555283, 795600716003, 235797558874, 11873025674, 0, 0] := by
  rw [show D2M8K2.u7811 = KTree.node D2M8K2.t7818 (nat_lit 16971990) (nat_lit 2286638863) (nat_lit 0) D2M8K2.t7819 from rfl, totK_node, tot7818, tot7819]
  decide +kernel

theorem arows7813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7813 = true := by
  rw [show D2M8K2.u7813 = KTree.node D2M8K2.t7820 (nat_lit 16973718) (nat_lit 3561165269) (nat_lit 0) D2M8K2.t7821 from rfl, allE_node, rows7820, irow7813, rows7821]
  all_goals rfl

theorem atot7813 : totK PD2M8K2 D2M8K2.u7813 = [0, 242333323372, 838766425882, 663352890314, 75042095813, 0, 0, 0] := by
  rw [show D2M8K2.u7813 = KTree.node D2M8K2.t7820 (nat_lit 16973718) (nat_lit 3561165269) (nat_lit 0) D2M8K2.t7821 from rfl, totK_node, tot7820, tot7821]
  decide +kernel

theorem arows7814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7814 = true := by
  rw [show D2M8K2.u7814 = KTree.node D2M8K2.t7822 (nat_lit 16975649) (nat_lit 1350974564) (nat_lit 2) D2M8K2.t7823 from rfl, allE_node, rows7822, irow7814, rows7823]
  all_goals rfl

theorem atot7814 : totK PD2M8K2 D2M8K2.u7814 = [0, 160134897378, 647125502253, 761851874299, 223645053295, 12040273252, 0, 0] := by
  rw [show D2M8K2.u7814 = KTree.node D2M8K2.t7822 (nat_lit 16975649) (nat_lit 1350974564) (nat_lit 2) D2M8K2.t7823 from rfl, totK_node, tot7822, tot7823]
  decide +kernel

theorem arows7818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7818 = true := by
  rw [show D2M8K2.u7818 = KTree.node D2M8K2.t7824 (nat_lit 16977032) (nat_lit 3713827311) (nat_lit 0) D2M8K2.t7825 from rfl, allE_node, rows7824, irow7818, rows7825]
  all_goals rfl

theorem atot7818 : totK PD2M8K2 D2M8K2.u7818 = [0, 262404754154, 814247115904, 613163728861, 96359386297, 1096156699, 0, 0] := by
  rw [show D2M8K2.u7818 = KTree.node D2M8K2.t7824 (nat_lit 16977032) (nat_lit 3713827311) (nat_lit 0) D2M8K2.t7825 from rfl, totK_node, tot7824, tot7825]
  decide +kernel

theorem arows7819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7819 = true := by
  rw [show D2M8K2.u7819 = KTree.node D2M8K2.t7826 (nat_lit 16978996) (nat_lit 3567991348) (nat_lit 0) D2M8K2.t7827 from rfl, allE_node, rows7826, irow7819, rows7827]
  all_goals rfl

theorem atot7819 : totK PD2M8K2 D2M8K2.u7819 = [0, 174823675156, 711923376376, 787301851954, 158631727530, 3880716147, 0, 0] := by
  rw [show D2M8K2.u7819 = KTree.node D2M8K2.t7826 (nat_lit 16978996) (nat_lit 3567991348) (nat_lit 0) D2M8K2.t7827 from rfl, totK_node, tot7826, tot7827]
  decide +kernel

theorem arows7821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7821 = true := by
  rw [show D2M8K2.u7821 = KTree.node D2M8K2.t7828 (nat_lit 16981404) (nat_lit 2494694859) (nat_lit 0) D2M8K2.t7829 from rfl, allE_node, rows7828, irow7821, rows7829]
  all_goals rfl

theorem atot7821 : totK PD2M8K2 D2M8K2.u7821 = [0, 158212545565, 694201009964, 796552255667, 185683648167, 4050001513, 0, 0] := by
  rw [show D2M8K2.u7821 = KTree.node D2M8K2.t7828 (nat_lit 16981404) (nat_lit 2494694859) (nat_lit 0) D2M8K2.t7829 from rfl, totK_node, tot7828, tot7829]
  decide +kernel

theorem arows7822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7822 = true := by
  rw [show D2M8K2.u7822 = KTree.node D2M8K2.t7830 (nat_lit 16986814) (nat_lit 3897375164) (nat_lit 0) D2M8K2.t7831 from rfl, allE_node, rows7830, irow7822, rows7831]
  all_goals rfl

theorem atot7822 : totK PD2M8K2 D2M8K2.u7822 = [0, 0, 345376742413, 902985424722, 525641918136, 46850647959, 0, 0] := by
  rw [show D2M8K2.u7822 = KTree.node D2M8K2.t7830 (nat_lit 16986814) (nat_lit 3897375164) (nat_lit 0) D2M8K2.t7831 from rfl, totK_node, tot7830, tot7831]
  decide +kernel

theorem arows7825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7825 = true := by
  rw [show D2M8K2.u7825 = KTree.node D2M8K2.t7832 (nat_lit 16988325) (nat_lit 1383261414) (nat_lit 0) D2M8K2.t7833 from rfl, allE_node, rows7832, irow7825, rows7833]
  all_goals rfl

theorem atot7825 : totK PD2M8K2 D2M8K2.u7825 = [0, 0, 154856210001, 663476566592, 751029533098, 240236475784, 13735775371, 0] := by
  rw [show D2M8K2.u7825 = KTree.node D2M8K2.t7832 (nat_lit 16988325) (nat_lit 1383261414) (nat_lit 0) D2M8K2.t7833 from rfl, totK_node, tot7832, tot7833]
  decide +kernel

theorem arows7826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7826 = true := by
  rw [show D2M8K2.u7826 = KTree.node D2M8K2.t7834 (nat_lit 16989962) (nat_lit 3150067071) (nat_lit 0) D2M8K2.t7835 from rfl, allE_node, rows7834, irow7826, rows7835]
  all_goals rfl

theorem atot7826 : totK PD2M8K2 D2M8K2.u7826 = [0, 0, 248720122746, 798156100801, 653910086277, 124400305487, 1353333895, 0] := by
  rw [show D2M8K2.u7826 = KTree.node D2M8K2.t7834 (nat_lit 16989962) (nat_lit 3150067071) (nat_lit 0) D2M8K2.t7835 from rfl, totK_node, tot7834, tot7835]
  decide +kernel

theorem arows7828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7828 = true := by
  rw [show D2M8K2.u7828 = KTree.node D2M8K2.t7836 (nat_lit 16991442) (nat_lit 2307171572) (nat_lit 0) D2M8K2.t7837 from rfl, allE_node, rows7836, irow7828, rows7837]
  all_goals rfl

theorem atot7828 : totK PD2M8K2 D2M8K2.u7828 = [0, 0, 166478180780, 741139331115, 750251698027, 138749321115, 4009909289, 0] := by
  rw [show D2M8K2.u7828 = KTree.node D2M8K2.t7836 (nat_lit 16991442) (nat_lit 2307171572) (nat_lit 0) D2M8K2.t7837 from rfl, totK_node, tot7836, tot7837]
  decide +kernel

theorem arows7829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7829 = true := by
  rw [show D2M8K2.u7829 = KTree.node D2M8K2.t7838 (nat_lit 16993573) (nat_lit 619373902) (nat_lit 0) D2M8K2.t7839 from rfl, allE_node, rows7838, irow7829, rows7839]
  all_goals rfl

theorem atot7829 : totK PD2M8K2 D2M8K2.u7829 = [0, 0, 297070399150, 803965746472, 598326427524, 98375239554, 1149959346, 0] := by
  rw [show D2M8K2.u7829 = KTree.node D2M8K2.t7838 (nat_lit 16993573) (nat_lit 619373902) (nat_lit 0) D2M8K2.t7839 from rfl, totK_node, tot7838, tot7839]
  decide +kernel

theorem arows7834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7834 = true := by
  rw [show D2M8K2.u7834 = KTree.node D2M8K2.t7840 (nat_lit 16996929) (nat_lit 1834342295) (nat_lit 0) D2M8K2.t7841 from rfl, allE_node, rows7840, irow7834, rows7841]
  all_goals rfl

theorem atot7834 : totK PD2M8K2 D2M8K2.u7834 = [0, 0, 331366946909, 914606782738, 523172971406, 42464881743, 0, 0] := by
  rw [show D2M8K2.u7834 = KTree.node D2M8K2.t7840 (nat_lit 16996929) (nat_lit 1834342295) (nat_lit 0) D2M8K2.t7841 from rfl, totK_node, tot7840, tot7841]
  decide +kernel

theorem arows7835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7835 = true := by
  rw [show D2M8K2.u7835 = KTree.node D2M8K2.t7842 (nat_lit 16998356) (nat_lit 3182848330) (nat_lit 0) D2M8K2.t7843 from rfl, allE_node, rows7842, irow7835, rows7843]
  all_goals rfl

theorem atot7835 : totK PD2M8K2 D2M8K2.u7835 = [0, 0, 172196230041, 805489983497, 743729377949, 72397163174, 0, 0] := by
  rw [show D2M8K2.u7835 = KTree.node D2M8K2.t7842 (nat_lit 16998356) (nat_lit 3182848330) (nat_lit 0) D2M8K2.t7843 from rfl, totK_node, tot7842, tot7843]
  decide +kernel

theorem arows7837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7837 = true := by
  rw [show D2M8K2.u7837 = KTree.node D2M8K2.t7844 (nat_lit 17000693) (nat_lit 2401304114) (nat_lit 0) D2M8K2.t7845 from rfl, allE_node, rows7844, irow7837, rows7845]
  all_goals rfl

theorem atot7837 : totK PD2M8K2 D2M8K2.u7837 = [0, 0, 332215697777, 842830387954, 571270191553, 102449596722, 1415142070, 0] := by
  rw [show D2M8K2.u7837 = KTree.node D2M8K2.t7844 (nat_lit 17000693) (nat_lit 2401304114) (nat_lit 0) D2M8K2.t7845 from rfl, totK_node, tot7844, tot7845]
  decide +kernel

theorem arows7838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7838 = true := by
  rw [show D2M8K2.u7838 = KTree.node D2M8K2.t7846 (nat_lit 17004296) (nat_lit 3604144343) (nat_lit 0) D2M8K2.t7847 from rfl, allE_node, rows7846, irow7838, rows7847]
  all_goals rfl

theorem atot7838 : totK PD2M8K2 D2M8K2.u7838 = [0, 346255259307, 847864139576, 459648018000, 108163948780, 10798778176, 0, 0] := by
  rw [show D2M8K2.u7838 = KTree.node D2M8K2.t7846 (nat_lit 17004296) (nat_lit 3604144343) (nat_lit 0) D2M8K2.t7847 from rfl, totK_node, tot7846, tot7847]
  decide +kernel

theorem arows7841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7841 = true := by
  rw [show D2M8K2.u7841 = KTree.node D2M8K2.t7848 (nat_lit 17005888) (nat_lit 3764259779) (nat_lit 0) D2M8K2.t7849 from rfl, allE_node, rows7848, irow7841, rows7849]
  all_goals rfl

theorem atot7841 : totK PD2M8K2 D2M8K2.u7841 = [0, 119894139755, 681220380698, 846081875891, 145297545747, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7841 = KTree.node D2M8K2.t7848 (nat_lit 17005888) (nat_lit 3764259779) (nat_lit 0) D2M8K2.t7849 from rfl, totK_node, tot7848, tot7849]
  decide +kernel

theorem arows7842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7842 = true := by
  rw [show D2M8K2.u7842 = KTree.node D2M8K2.t7850 (nat_lit 17007943) (nat_lit 2369530220) (nat_lit 0) D2M8K2.t7851 from rfl, allE_node, rows7850, irow7842, rows7851]
  all_goals rfl

theorem atot7842 : totK PD2M8K2 D2M8K2.u7842 = [0, 355447039512, 932665451529, 508370764865, 41681457844, 0, 0, 0] := by
  rw [show D2M8K2.u7842 = KTree.node D2M8K2.t7850 (nat_lit 17007943) (nat_lit 2369530220) (nat_lit 0) D2M8K2.t7851 from rfl, totK_node, tot7850, tot7851]
  decide +kernel

theorem arows7844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7844 = true := by
  rw [show D2M8K2.u7844 = KTree.node D2M8K2.t7852 (nat_lit 17009429) (nat_lit 1278131303) (nat_lit 0) D2M8K2.t7853 from rfl, allE_node, rows7852, irow7844, rows7853]
  all_goals rfl

theorem atot7844 : totK PD2M8K2 D2M8K2.u7844 = [0, 0, 397635165155, 935100415522, 445784274768, 30543407097, 0, 0] := by
  rw [show D2M8K2.u7844 = KTree.node D2M8K2.t7852 (nat_lit 17009429) (nat_lit 1278131303) (nat_lit 0) D2M8K2.t7853 from rfl, totK_node, tot7852, tot7853]
  decide +kernel

theorem arows7845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7845 = true := by
  rw [show D2M8K2.u7845 = KTree.node D2M8K2.t7854 (nat_lit 17010803) (nat_lit 2550439259) (nat_lit 0) D2M8K2.t7855 from rfl, allE_node, rows7854, irow7845, rows7855]
  all_goals rfl

theorem atot7845 : totK PD2M8K2 D2M8K2.u7845 = [0, 304606632667, 807212479279, 580218545021, 139537363540, 5356395648, 0, 0] := by
  rw [show D2M8K2.u7845 = KTree.node D2M8K2.t7854 (nat_lit 17010803) (nat_lit 2550439259) (nat_lit 0) D2M8K2.t7855 from rfl, totK_node, tot7854, tot7855]
  decide +kernel

theorem arows7849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7849 = true := by
  rw [show D2M8K2.u7849 = KTree.node D2M8K2.t7856 (nat_lit 17012261) (nat_lit 2299357354) (nat_lit 0) D2M8K2.t7857 from rfl, allE_node, rows7856, irow7849, rows7857]
  all_goals rfl

theorem atot7849 : totK PD2M8K2 D2M8K2.u7849 = [0, 136429283381, 653120439843, 797257247516, 207275702550, 9587713104, 0, 0] := by
  rw [show D2M8K2.u7849 = KTree.node D2M8K2.t7856 (nat_lit 17012261) (nat_lit 2299357354) (nat_lit 0) D2M8K2.t7857 from rfl, totK_node, tot7856, tot7857]
  decide +kernel

theorem arows7850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7850 = true := by
  rw [show D2M8K2.u7850 = KTree.node D2M8K2.t7858 (nat_lit 17017504) (nat_lit 2812633341) (nat_lit 0) D2M8K2.t7859 from rfl, allE_node, rows7858, irow7850, rows7859]
  all_goals rfl

theorem atot7850 : totK PD2M8K2 D2M8K2.u7850 = [0, 261400460006, 778613885732, 643563176762, 124296089187, 3462014130, 0, 0] := by
  rw [show D2M8K2.u7850 = KTree.node D2M8K2.t7858 (nat_lit 17017504) (nat_lit 2812633341) (nat_lit 0) D2M8K2.t7859 from rfl, totK_node, tot7858, tot7859]
  decide +kernel

theorem arows7852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7852 = true := by
  rw [show D2M8K2.u7852 = KTree.node D2M8K2.t7860 (nat_lit 17018742) (nat_lit 3723911047) (nat_lit 0) D2M8K2.t7861 from rfl, allE_node, rows7860, irow7852, rows7861]
  all_goals rfl

theorem atot7852 : totK PD2M8K2 D2M8K2.u7852 = [0, 162674308024, 747278608625, 764145535069, 118205922412, 1096505104, 0, 0] := by
  rw [show D2M8K2.u7852 = KTree.node D2M8K2.t7860 (nat_lit 17018742) (nat_lit 3723911047) (nat_lit 0) D2M8K2.t7861 from rfl, totK_node, tot7860, tot7861]
  decide +kernel

theorem arows7853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7853 = true := by
  rw [show D2M8K2.u7853 = KTree.node D2M8K2.t7862 (nat_lit 17021044) (nat_lit 3552103341) (nat_lit 0) D2M8K2.t7863 from rfl, allE_node, rows7862, irow7853, rows7863]
  all_goals rfl

theorem atot7853 : totK PD2M8K2 D2M8K2.u7853 = [0, 256376081565, 786272182528, 640296169241, 128824228240, 3884009855, 0, 0] := by
  rw [show D2M8K2.u7853 = KTree.node D2M8K2.t7862 (nat_lit 17021044) (nat_lit 3552103341) (nat_lit 0) D2M8K2.t7863 from rfl, totK_node, tot7862, tot7863]
  decide +kernel

theorem arows7856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7856 = true := by
  rw [show D2M8K2.u7856 = KTree.node D2M8K2.t7864 (nat_lit 17022874) (nat_lit 3950404598) (nat_lit 0) D2M8K2.t7865 from rfl, allE_node, rows7864, irow7856, rows7865]
  all_goals rfl

theorem atot7856 : totK PD2M8K2 D2M8K2.u7856 = [0, 89240473698, 584820191104, 878905469200, 249788169947, 6195912385, 0, 0] := by
  rw [show D2M8K2.u7856 = KTree.node D2M8K2.t7864 (nat_lit 17022874) (nat_lit 3950404598) (nat_lit 0) D2M8K2.t7865 from rfl, totK_node, tot7864, tot7865]
  decide +kernel

theorem arows7857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7857 = true := by
  rw [show D2M8K2.u7857 = KTree.node D2M8K2.t7866 (nat_lit 17025090) (nat_lit 1395987329) (nat_lit 0) D2M8K2.t7867 from rfl, allE_node, rows7866, irow7857, rows7867]
  all_goals rfl

theorem atot7857 : totK PD2M8K2 D2M8K2.u7857 = [0, 0, 386100677601, 934841945315, 407687522507, 22573526938, 0, 0] := by
  rw [show D2M8K2.u7857 = KTree.node D2M8K2.t7866 (nat_lit 17025090) (nat_lit 1395987329) (nat_lit 0) D2M8K2.t7867 from rfl, totK_node, tot7866, tot7867]
  decide +kernel

theorem arows7859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7859 = true := by
  rw [show D2M8K2.u7859 = KTree.node D2M8K2.t7868 (nat_lit 17026868) (nat_lit 2987518644) (nat_lit 0) D2M8K2.t7869 from rfl, allE_node, rows7868, irow7859, rows7869]
  all_goals rfl

theorem atot7859 : totK PD2M8K2 D2M8K2.u7859 = [0, 0, 111734167256, 713795476091, 801227598874, 118707873272, 1206465782, 0] := by
  rw [show D2M8K2.u7859 = KTree.node D2M8K2.t7868 (nat_lit 17026868) (nat_lit 2987518644) (nat_lit 0) D2M8K2.t7869 from rfl, totK_node, tot7868, tot7869]
  decide +kernel

theorem arows7860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7860 = true := by
  rw [show D2M8K2.u7860 = KTree.node D2M8K2.t7870 (nat_lit 17028898) (nat_lit 3483099730) (nat_lit 0) D2M8K2.t7871 from rfl, allE_node, rows7870, irow7860, rows7871]
  all_goals rfl

theorem atot7860 : totK PD2M8K2 D2M8K2.u7860 = [0, 0, 391788239956, 955039816311, 450816864849, 26831813920, 0, 0] := by
  rw [show D2M8K2.u7860 = KTree.node D2M8K2.t7870 (nat_lit 17028898) (nat_lit 3483099730) (nat_lit 0) D2M8K2.t7871 from rfl, totK_node, tot7870, tot7871]
  decide +kernel

theorem arows7866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7866 = true := by
  rw [show D2M8K2.u7866 = KTree.node D2M8K2.t7872 (nat_lit 17031870) (nat_lit 2927246573) (nat_lit 0) D2M8K2.t7873 from rfl, allE_node, rows7872, irow7866, rows7873]
  all_goals rfl

theorem atot7866 : totK PD2M8K2 D2M8K2.u7866 = [0, 0, 371147852835, 958518260368, 455845290838, 28288117611, 0, 0] := by
  rw [show D2M8K2.u7866 = KTree.node D2M8K2.t7872 (nat_lit 17031870) (nat_lit 2927246573) (nat_lit 0) D2M8K2.t7873 from rfl, totK_node, tot7872, tot7873]
  decide +kernel

theorem arows7867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7867 = true := by
  rw [show D2M8K2.u7867 = KTree.node D2M8K2.t7874 (nat_lit 17033569) (nat_lit 1441057791) (nat_lit 0) D2M8K2.t7875 from rfl, allE_node, rows7874, irow7867, rows7875]
  all_goals rfl

theorem atot7867 : totK PD2M8K2 D2M8K2.u7867 = [0, 0, 7518713851, 495177564585, 933861075154, 280069354355, 13016197374, 0] := by
  rw [show D2M8K2.u7867 = KTree.node D2M8K2.t7874 (nat_lit 17033569) (nat_lit 1441057791) (nat_lit 0) D2M8K2.t7875 from rfl, totK_node, tot7874, tot7875]
  decide +kernel

theorem arows7869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7869 = true := by
  rw [show D2M8K2.u7869 = KTree.node D2M8K2.t7876 (nat_lit 17038699) (nat_lit 1602493091) (nat_lit 0) D2M8K2.t7877 from rfl, allE_node, rows7876, irow7869, rows7877]
  all_goals rfl

theorem atot7869 : totK PD2M8K2 D2M8K2.u7869 = [0, 0, 402659271538, 951216007354, 417724324586, 23120255374, 0, 0] := by
  rw [show D2M8K2.u7869 = KTree.node D2M8K2.t7876 (nat_lit 17038699) (nat_lit 1602493091) (nat_lit 0) D2M8K2.t7877 from rfl, totK_node, tot7876, tot7877]
  decide +kernel

theorem arows7870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7870 = true := by
  rw [show D2M8K2.u7870 = KTree.node D2M8K2.t7878 (nat_lit 17040480) (nat_lit 3436952923) (nat_lit 0) D2M8K2.t7879 from rfl, allE_node, rows7878, irow7870, rows7879]
  all_goals rfl

theorem atot7870 : totK PD2M8K2 D2M8K2.u7870 = [0, 0, 92408129233, 657041515906, 799016160547, 153919234009, 4574395652, 0] := by
  rw [show D2M8K2.u7870 = KTree.node D2M8K2.t7878 (nat_lit 17040480) (nat_lit 3436952923) (nat_lit 0) D2M8K2.t7879 from rfl, totK_node, tot7878, tot7879]
  decide +kernel

theorem arows7873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7873 = true := by
  rw [show D2M8K2.u7873 = KTree.node D2M8K2.t7880 (nat_lit 17042324) (nat_lit 2834312237) (nat_lit 0) D2M8K2.t7881 from rfl, allE_node, rows7880, irow7873, rows7881]
  all_goals rfl

theorem atot7873 : totK PD2M8K2 D2M8K2.u7873 = [0, 89273601505, 488995045177, 818418195919, 402287760665, 30227327220, 0, 0] := by
  rw [show D2M8K2.u7873 = KTree.node D2M8K2.t7880 (nat_lit 17042324) (nat_lit 2834312237) (nat_lit 0) D2M8K2.t7881 from rfl, totK_node, tot7880, tot7881]
  decide +kernel

theorem arows7874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7874 = true := by
  rw [show D2M8K2.u7874 = KTree.node D2M8K2.t7882 (nat_lit 17046203) (nat_lit 1878131693) (nat_lit 0) D2M8K2.t7883 from rfl, allE_node, rows7882, irow7874, rows7883]
  all_goals rfl

theorem atot7874 : totK PD2M8K2 D2M8K2.u7874 = [0, 302478382232, 866276002510, 546392403227, 52772813259, 0, 0, 0] := by
  rw [show D2M8K2.u7874 = KTree.node D2M8K2.t7882 (nat_lit 17046203) (nat_lit 1878131693) (nat_lit 0) D2M8K2.t7883 from rfl, totK_node, tot7882, tot7883]
  decide +kernel

theorem arows7876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7876 = true := by
  rw [show D2M8K2.u7876 = KTree.node D2M8K2.t7884 (nat_lit 17048282) (nat_lit 3413354070) (nat_lit 0) D2M8K2.t7885 from rfl, allE_node, rows7884, irow7876, rows7885]
  all_goals rfl

theorem atot7876 : totK PD2M8K2 D2M8K2.u7876 = [0, 165681710033, 724679980614, 800442511623, 125632854580, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7876 = KTree.node D2M8K2.t7884 (nat_lit 17048282) (nat_lit 3413354070) (nat_lit 0) D2M8K2.t7885 from rfl, totK_node, tot7884, tot7885]
  decide +kernel

theorem arows7877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7877 = true := by
  rw [show D2M8K2.u7877 = KTree.node D2M8K2.t7886 (nat_lit 17049940) (nat_lit 3893431640) (nat_lit 0) D2M8K2.t7887 from rfl, allE_node, rows7886, irow7877, rows7887]
  all_goals rfl

theorem atot7877 : totK PD2M8K2 D2M8K2.u7877 = [0, 237659676607, 776113230497, 650071122336, 164339350322, 9977052014, 0, 0] := by
  rw [show D2M8K2.u7877 = KTree.node D2M8K2.t7886 (nat_lit 17049940) (nat_lit 3893431640) (nat_lit 0) D2M8K2.t7887 from rfl, totK_node, tot7886, tot7887]
  decide +kernel

theorem arows7881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7881 = true := by
  rw [show D2M8K2.u7881 = KTree.node D2M8K2.t7888 (nat_lit 17051668) (nat_lit 3893431640) (nat_lit 0) D2M8K2.t7889 from rfl, allE_node, rows7888, irow7881, rows7889]
  all_goals rfl

theorem atot7881 : totK PD2M8K2 D2M8K2.u7881 = [0, 172450032168, 666244153846, 753363714058, 222097979460, 5430665091, 0, 0] := by
  rw [show D2M8K2.u7881 = KTree.node D2M8K2.t7888 (nat_lit 17051668) (nat_lit 3893431640) (nat_lit 0) D2M8K2.t7889 from rfl, totK_node, tot7888, tot7889]
  decide +kernel

theorem arows7882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7882 = true := by
  rw [show D2M8K2.u7882 = KTree.node D2M8K2.t7890 (nat_lit 17056728) (nat_lit 3394814948) (nat_lit 0) D2M8K2.t7891 from rfl, allE_node, rows7890, irow7882, rows7891]
  all_goals rfl

theorem atot7882 : totK PD2M8K2 D2M8K2.u7882 = [0, 253495487828, 797208072854, 644630498530, 105047933938, 1198073392, 0, 0] := by
  rw [show D2M8K2.u7882 = KTree.node D2M8K2.t7890 (nat_lit 17056728) (nat_lit 3394814948) (nat_lit 0) D2M8K2.t7891 from rfl, totK_node, tot7890, tot7891]
  decide +kernel

theorem arows7884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7884 = true := by
  rw [show D2M8K2.u7884 = KTree.node D2M8K2.t7892 (nat_lit 17058415) (nat_lit 1889889520) (nat_lit 0) D2M8K2.t7893 from rfl, allE_node, rows7892, irow7884, rows7893]
  all_goals rfl

theorem atot7884 : totK PD2M8K2 D2M8K2.u7884 = [0, 156857624109, 630281287129, 759430074698, 226639072511, 12052611869, 0, 0] := by
  rw [show D2M8K2.u7884 = KTree.node D2M8K2.t7892 (nat_lit 17058415) (nat_lit 1889889520) (nat_lit 0) D2M8K2.t7893 from rfl, totK_node, tot7892, tot7893]
  decide +kernel

theorem arows7885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7885 = true := by
  rw [show D2M8K2.u7885 = KTree.node D2M8K2.t7894 (nat_lit 17059825) (nat_lit 1525900410) (nat_lit 0) D2M8K2.t7895 from rfl, allE_node, rows7894, irow7885, rows7895]
  all_goals rfl

theorem atot7885 : totK PD2M8K2 D2M8K2.u7885 = [0, 266459789200, 835309501496, 610333901082, 79002836916, 1096505104, 0, 0] := by
  rw [show D2M8K2.u7885 = KTree.node D2M8K2.t7894 (nat_lit 17059825) (nat_lit 1525900410) (nat_lit 0) D2M8K2.t7895 from rfl, totK_node, tot7894, tot7895]
  decide +kernel

theorem arows7888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7888 = true := by
  rw [show D2M8K2.u7888 = KTree.node D2M8K2.t7896 (nat_lit 17061776) (nat_lit 3823420766) (nat_lit 0) D2M8K2.t7897 from rfl, allE_node, rows7896, irow7888, rows7897]
  all_goals rfl

theorem atot7888 : totK PD2M8K2 D2M8K2.u7888 = [0, 0, 490755564924, 1015082609114, 283278552912, 6403024948, 0, 0] := by
  rw [show D2M8K2.u7888 = KTree.node D2M8K2.t7896 (nat_lit 17061776) (nat_lit 3823420766) (nat_lit 0) D2M8K2.t7897 from rfl, totK_node, tot7896, tot7897]
  decide +kernel

theorem arows7889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7889 = true := by
  rw [show D2M8K2.u7889 = KTree.node D2M8K2.t7898 (nat_lit 17067169) (nat_lit 1562614071) (nat_lit 0) D2M8K2.t7899 from rfl, allE_node, rows7898, irow7889, rows7899]
  all_goals rfl

theorem atot7889 : totK PD2M8K2 D2M8K2.u7889 = [0, 0, 238501532937, 823495484452, 594026394756, 65788421756, 1239866073, 0] := by
  rw [show D2M8K2.u7889 = KTree.node D2M8K2.t7898 (nat_lit 17067169) (nat_lit 1562614071) (nat_lit 0) D2M8K2.t7899 from rfl, totK_node, tot7898, tot7899]
  decide +kernel

theorem arows7891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7891 = true := by
  rw [show D2M8K2.u7891 = KTree.node D2M8K2.t7900 (nat_lit 17069733) (nat_lit 1396636999) (nat_lit 0) D2M8K2.t7901 from rfl, allE_node, rows7900, irow7891, rows7901]
  all_goals rfl

theorem atot7891 : totK PD2M8K2 D2M8K2.u7891 = [0, 0, 282102220876, 880103175683, 596018311596, 53613457536, 0, 0] := by
  rw [show D2M8K2.u7891 = KTree.node D2M8K2.t7900 (nat_lit 17069733) (nat_lit 1396636999) (nat_lit 0) D2M8K2.t7901 from rfl, totK_node, tot7900, tot7901]
  decide +kernel

theorem arows7892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7892 = true := by
  rw [show D2M8K2.u7892 = KTree.node D2M8K2.t7902 (nat_lit 17076245) (nat_lit 1604773552) (nat_lit 0) D2M8K2.t7903 from rfl, allE_node, rows7902, irow7892, rows7903]
  all_goals rfl

theorem atot7892 : totK PD2M8K2 D2M8K2.u7892 = [0, 0, 385329390852, 965789135634, 439904275241, 22849383743, 0, 0] := by
  rw [show D2M8K2.u7892 = KTree.node D2M8K2.t7902 (nat_lit 17076245) (nat_lit 1604773552) (nat_lit 0) D2M8K2.t7903 from rfl, totK_node, tot7902, tot7903]
  decide +kernel

theorem arows7897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7897 = true := by
  rw [show D2M8K2.u7897 = KTree.node D2M8K2.t7904 (nat_lit 17079556) (nat_lit 3633973278) (nat_lit 0) D2M8K2.t7905 from rfl, allE_node, rows7904, irow7897, rows7905]
  all_goals rfl

theorem atot7897 : totK PD2M8K2 D2M8K2.u7897 = [0, 0, 364508834445, 943267041824, 454091859838, 26230041397, 0, 0] := by
  rw [show D2M8K2.u7897 = KTree.node D2M8K2.t7904 (nat_lit 17079556) (nat_lit 3633973278) (nat_lit 0) D2M8K2.t7905 from rfl, totK_node, tot7904, tot7905]
  decide +kernel

theorem arows7898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7898 = true := by
  rw [show D2M8K2.u7898 = KTree.node D2M8K2.t7906 (nat_lit 17080802) (nat_lit 4074876605) (nat_lit 0) D2M8K2.t7907 from rfl, allE_node, rows7906, irow7898, rows7907]
  all_goals rfl

theorem atot7898 : totK PD2M8K2 D2M8K2.u7898 = [0, 0, 216154779393, 819114401727, 626408511355, 76953606688, 1053411165, 0] := by
  rw [show D2M8K2.u7898 = KTree.node D2M8K2.t7906 (nat_lit 17080802) (nat_lit 4074876605) (nat_lit 0) D2M8K2.t7907 from rfl, totK_node, tot7906, tot7907]
  decide +kernel

theorem arows7900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7900 = true := by
  rw [show D2M8K2.u7900 = KTree.node D2M8K2.t7908 (nat_lit 17086616) (nat_lit 3514548927) (nat_lit 0) D2M8K2.t7909 from rfl, allE_node, rows7908, irow7900, rows7909]
  all_goals rfl

theorem atot7900 : totK PD2M8K2 D2M8K2.u7900 = [0, 259544195218, 621679352920, 433637331274, 342243228192, 92199291644, 3667207281, 0] := by
  rw [show D2M8K2.u7900 = KTree.node D2M8K2.t7908 (nat_lit 17086616) (nat_lit 3514548927) (nat_lit 0) D2M8K2.t7909 from rfl, totK_node, tot7908, tot7909]
  decide +kernel

theorem arows7901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7901 = true := by
  rw [show D2M8K2.u7901 = KTree.node D2M8K2.t7910 (nat_lit 17088198) (nat_lit 3779087480) (nat_lit 0) D2M8K2.t7911 from rfl, allE_node, rows7910, irow7901, rows7911]
  all_goals rfl

theorem atot7901 : totK PD2M8K2 D2M8K2.u7901 = [0, 152883975043, 705342144299, 769977020373, 130112781806, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7901 = KTree.node D2M8K2.t7910 (nat_lit 17088198) (nat_lit 3779087480) (nat_lit 0) D2M8K2.t7911 from rfl, totK_node, tot7910, tot7911]
  decide +kernel

theorem arows7904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7904 = true := by
  rw [show D2M8K2.u7904 = KTree.node D2M8K2.t7912 (nat_lit 17090524) (nat_lit 3962582701) (nat_lit 0) D2M8K2.t7913 from rfl, allE_node, rows7912, irow7904, rows7913]
  all_goals rfl

theorem atot7904 : totK PD2M8K2 D2M8K2.u7904 = [0, 299183348300, 845871332933, 607440054164, 65321997929, 0, 0, 0] := by
  rw [show D2M8K2.u7904 = KTree.node D2M8K2.t7912 (nat_lit 17090524) (nat_lit 3962582701) (nat_lit 0) D2M8K2.t7913 from rfl, totK_node, tot7912, tot7913]
  decide +kernel

theorem arows7905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7905 = true := by
  rw [show D2M8K2.u7905 = KTree.node D2M8K2.t7914 (nat_lit 17092056) (nat_lit 2202659978) (nat_lit 0) D2M8K2.t7915 from rfl, allE_node, rows7914, irow7905, rows7915]
  all_goals rfl

theorem atot7905 : totK PD2M8K2 D2M8K2.u7905 = [0, 123537675262, 612659693361, 764128634770, 292986496249, 25127349078, 0, 0] := by
  rw [show D2M8K2.u7905 = KTree.node D2M8K2.t7914 (nat_lit 17092056) (nat_lit 2202659978) (nat_lit 0) D2M8K2.t7915 from rfl, totK_node, tot7914, tot7915]
  decide +kernel

theorem arows7907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7907 = true := by
  rw [show D2M8K2.u7907 = KTree.node D2M8K2.t7916 (nat_lit 17093313) (nat_lit 1133281247) (nat_lit 0) D2M8K2.t7917 from rfl, allE_node, rows7916, irow7907, rows7917]
  all_goals rfl

theorem atot7907 : totK PD2M8K2 D2M8K2.u7907 = [0, 172708002957, 605180215202, 730598208383, 282407376331, 10843021292, 0, 0] := by
  rw [show D2M8K2.u7907 = KTree.node D2M8K2.t7916 (nat_lit 17093313) (nat_lit 1133281247) (nat_lit 0) D2M8K2.t7917 from rfl, totK_node, tot7916, tot7917]
  decide +kernel

theorem arows7908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7908 = true := by
  rw [show D2M8K2.u7908 = KTree.node D2M8K2.t7918 (nat_lit 17094789) (nat_lit 1725962346) (nat_lit 0) D2M8K2.t7919 from rfl, allE_node, rows7918, irow7908, rows7919]
  all_goals rfl

theorem atot7908 : totK PD2M8K2 D2M8K2.u7908 = [0, 249027941444, 796530090228, 648015910215, 103760566572, 1164319620, 0, 0] := by
  rw [show D2M8K2.u7908 = KTree.node D2M8K2.t7918 (nat_lit 17094789) (nat_lit 1725962346) (nat_lit 0) D2M8K2.t7919 from rfl, totK_node, tot7918, tot7919]
  decide +kernel

theorem arows7912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7912 = true := by
  rw [show D2M8K2.u7912 = KTree.node D2M8K2.t7920 (nat_lit 17096544) (nat_lit 3661867763) (nat_lit 0) D2M8K2.t7921 from rfl, allE_node, rows7920, irow7912, rows7921]
  all_goals rfl

theorem atot7912 : totK PD2M8K2 D2M8K2.u7912 = [0, 170049229353, 644419009420, 734884025197, 221657496825, 11885407614, 0, 0] := by
  rw [show D2M8K2.u7912 = KTree.node D2M8K2.t7920 (nat_lit 17096544) (nat_lit 3661867763) (nat_lit 0) D2M8K2.t7921 from rfl, totK_node, tot7920, tot7921]
  decide +kernel

theorem arows7913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7913 = true := by
  rw [show D2M8K2.u7913 = KTree.node D2M8K2.t7922 (nat_lit 17098150) (nat_lit 1178109756) (nat_lit 0) D2M8K2.t7923 from rfl, allE_node, rows7922, irow7913, rows7923]
  all_goals rfl

theorem atot7913 : totK PD2M8K2 D2M8K2.u7913 = [0, 231071253058, 777417717837, 667591908148, 101582587017, 1198073392, 0, 0] := by
  rw [show D2M8K2.u7913 = KTree.node D2M8K2.t7922 (nat_lit 17098150) (nat_lit 1178109756) (nat_lit 0) D2M8K2.t7923 from rfl, totK_node, tot7922, tot7923]
  decide +kernel

theorem arows7915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7915 = true := by
  rw [show D2M8K2.u7915 = KTree.node D2M8K2.t7924 (nat_lit 17099954) (nat_lit 3635859514) (nat_lit 0) D2M8K2.t7925 from rfl, allE_node, rows7924, irow7915, rows7925]
  all_goals rfl

theorem atot7915 : totK PD2M8K2 D2M8K2.u7915 = [0, 175967501358, 658889765822, 726832934992, 215562543855, 12052611869, 0, 0] := by
  rw [show D2M8K2.u7915 = KTree.node D2M8K2.t7924 (nat_lit 17099954) (nat_lit 3635859514) (nat_lit 0) D2M8K2.t7925 from rfl, totK_node, tot7924, tot7925]
  decide +kernel

theorem arows7916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7916 = true := by
  rw [show D2M8K2.u7916 = KTree.node D2M8K2.t7926 (nat_lit 17101328) (nat_lit 3691383965) (nat_lit 0) D2M8K2.t7927 from rfl, allE_node, rows7926, irow7916, rows7927]
  all_goals rfl

theorem atot7916 : totK PD2M8K2 D2M8K2.u7916 = [0, 268360367569, 823644850038, 626075261914, 84843833637, 1096505104, 0, 0] := by
  rw [show D2M8K2.u7916 = KTree.node D2M8K2.t7926 (nat_lit 17101328) (nat_lit 3691383965) (nat_lit 0) D2M8K2.t7927 from rfl, totK_node, tot7926, tot7927]
  decide +kernel

theorem arows7919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7919 = true := by
  rw [show D2M8K2.u7919 = KTree.node D2M8K2.t7928 (nat_lit 17103253) (nat_lit 1169642120) (nat_lit 0) D2M8K2.t7929 from rfl, allE_node, rows7928, irow7919, rows7929]
  all_goals rfl

theorem atot7919 : totK PD2M8K2 D2M8K2.u7919 = [0, 0, 529046668927, 1023241531913, 262038920656, 5253830308, 0, 0] := by
  rw [show D2M8K2.u7919 = KTree.node D2M8K2.t7928 (nat_lit 17103253) (nat_lit 1169642120) (nat_lit 0) D2M8K2.t7929 from rfl, totK_node, tot7928, tot7929]
  decide +kernel

theorem arows7920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7920 = true := by
  rw [show D2M8K2.u7920 = KTree.node D2M8K2.t7930 (nat_lit 17108528) (nat_lit 3798690481) (nat_lit 0) D2M8K2.t7931 from rfl, allE_node, rows7930, irow7920, rows7931]
  all_goals rfl

theorem atot7920 : totK PD2M8K2 D2M8K2.u7920 = [0, 0, 235259095398, 794574490811, 587664524220, 81736401388, 1138244013, 0] := by
  rw [show D2M8K2.u7920 = KTree.node D2M8K2.t7930 (nat_lit 17108528) (nat_lit 3798690481) (nat_lit 0) D2M8K2.t7931 from rfl, totK_node, tot7930, tot7931]
  decide +kernel

theorem arows7922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7922 = true := by
  rw [show D2M8K2.u7922 = KTree.node D2M8K2.t7932 (nat_lit 17111126) (nat_lit 4150964372) (nat_lit 0) D2M8K2.t7933 from rfl, allE_node, rows7932, irow7922, rows7933]
  all_goals rfl

theorem atot7922 : totK PD2M8K2 D2M8K2.u7922 = [0, 0, 265010938203, 863886092909, 594739679352, 56934820937, 0, 0] := by
  rw [show D2M8K2.u7922 = KTree.node D2M8K2.t7932 (nat_lit 17111126) (nat_lit 4150964372) (nat_lit 0) D2M8K2.t7933 from rfl, totK_node, tot7932, tot7933]
  decide +kernel

theorem arows7923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7923 = true := by
  rw [show D2M8K2.u7923 = KTree.node D2M8K2.t7934 (nat_lit 17114123) (nat_lit 2857538154) (nat_lit 0) D2M8K2.t7935 from rfl, allE_node, rows7934, irow7923, rows7935]
  all_goals rfl

theorem atot7923 : totK PD2M8K2 D2M8K2.u7923 = [0, 0, 365190731896, 968801868928, 451965538370, 22495915122, 0, 0] := by
  rw [show D2M8K2.u7923 = KTree.node D2M8K2.t7934 (nat_lit 17114123) (nat_lit 2857538154) (nat_lit 0) D2M8K2.t7935 from rfl, totK_node, tot7934, tot7935]
  decide +kernel

theorem arows7931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7931 = true := by
  rw [show D2M8K2.u7931 = KTree.node D2M8K2.t7936 (nat_lit 17115616) (nat_lit 3756584681) (nat_lit 0) D2M8K2.t7937 from rfl, allE_node, rows7936, irow7931, rows7937]
  all_goals rfl

theorem atot7931 : totK PD2M8K2 D2M8K2.u7931 = [0, 0, 380726551908, 952772582840, 424377742218, 22911640103, 0, 0] := by
  rw [show D2M8K2.u7931 = KTree.node D2M8K2.t7936 (nat_lit 17115616) (nat_lit 3756584681) (nat_lit 0) D2M8K2.t7937 from rfl, totK_node, tot7936, tot7937]
  decide +kernel

theorem arows7932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7932 = true := by
  rw [show D2M8K2.u7932 = KTree.node D2M8K2.t7938 (nat_lit 17118916) (nat_lit 3766264988) (nat_lit 0) D2M8K2.t7939 from rfl, allE_node, rows7938, irow7932, rows7939]
  all_goals rfl

theorem atot7932 : totK PD2M8K2 D2M8K2.u7932 = [0, 0, 386074031615, 951777482266, 422142876811, 19169978529, 0, 0] := by
  rw [show D2M8K2.u7932 = KTree.node D2M8K2.t7938 (nat_lit 17118916) (nat_lit 3766264988) (nat_lit 0) D2M8K2.t7939 from rfl, totK_node, tot7938, tot7939]
  decide +kernel

theorem arows7934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7934 = true := by
  rw [show D2M8K2.u7934 = KTree.node D2M8K2.t7940 (nat_lit 17121998) (nat_lit 3801413609) (nat_lit 0) D2M8K2.t7941 from rfl, allE_node, rows7940, irow7934, rows7941]
  all_goals rfl

theorem atot7934 : totK PD2M8K2 D2M8K2.u7934 = [0, 0, 281962818754, 890008679970, 557026589048, 49833812471, 0, 0] := by
  rw [show D2M8K2.u7934 = KTree.node D2M8K2.t7940 (nat_lit 17121998) (nat_lit 3801413609) (nat_lit 0) D2M8K2.t7941 from rfl, totK_node, tot7940, tot7941]
  decide +kernel

theorem arows7935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7935 = true := by
  rw [show D2M8K2.u7935 = KTree.node D2M8K2.t7942 (nat_lit 17123961) (nat_lit 1864447005) (nat_lit 0) D2M8K2.t7943 from rfl, allE_node, rows7942, irow7935, rows7943]
  all_goals rfl

theorem atot7935 : totK PD2M8K2 D2M8K2.u7935 = [0, 0, 167804228932, 689005764717, 732782364486, 175006453837, 4977114383, 0] := by
  rw [show D2M8K2.u7935 = KTree.node D2M8K2.t7942 (nat_lit 17123961) (nat_lit 1864447005) (nat_lit 0) D2M8K2.t7943 from rfl, totK_node, tot7942, tot7943]
  decide +kernel

theorem arows7938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7938 = true := by
  rw [show D2M8K2.u7938 = KTree.node D2M8K2.t7944 (nat_lit 17170676) (nat_lit 3698774642) (nat_lit 0) D2M8K2.t7945 from rfl, allE_node, rows7944, irow7938, rows7945]
  all_goals rfl

theorem atot7938 : totK PD2M8K2 D2M8K2.u7938 = [0, 0, 259509122425, 840162448836, 582048236016, 71683322590, 1369150432, 0] := by
  rw [show D2M8K2.u7938 = KTree.node D2M8K2.t7944 (nat_lit 17170676) (nat_lit 3698774642) (nat_lit 0) D2M8K2.t7945 from rfl, totK_node, tot7944, tot7945]
  decide +kernel

theorem arows7939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7939 = true := by
  rw [show D2M8K2.u7939 = KTree.node D2M8K2.t7946 (nat_lit 17172644) (nat_lit 2532168262) (nat_lit 0) D2M8K2.t7947 from rfl, allE_node, rows7946, irow7939, rows7947]
  all_goals rfl

theorem atot7939 : totK PD2M8K2 D2M8K2.u7939 = [0, 0, 173337114409, 754086450177, 767508416606, 93491065554, 0, 0] := by
  rw [show D2M8K2.u7939 = KTree.node D2M8K2.t7946 (nat_lit 17172644) (nat_lit 2532168262) (nat_lit 0) D2M8K2.t7947 from rfl, totK_node, tot7946, tot7947]
  decide +kernel

theorem arows7941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7941 = true := by
  rw [show D2M8K2.u7941 = KTree.node D2M8K2.t7948 (nat_lit 17177805) (nat_lit 1069561097) (nat_lit 0) D2M8K2.t7949 from rfl, allE_node, rows7948, irow7941, rows7949]
  all_goals rfl

theorem atot7941 : totK PD2M8K2 D2M8K2.u7941 = [0, 0, 237951974367, 795527022131, 648182085375, 95749402215, 1164319620, 0] := by
  rw [show D2M8K2.u7941 = KTree.node D2M8K2.t7948 (nat_lit 17177805) (nat_lit 1069561097) (nat_lit 0) D2M8K2.t7949 from rfl, totK_node, tot7948, tot7949]
  decide +kernel

theorem arows7942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7942 = true := by
  rw [show D2M8K2.u7942 = KTree.node D2M8K2.t7950 (nat_lit 17179544) (nat_lit 2821574432) (nat_lit 0) D2M8K2.t7951 from rfl, allE_node, rows7950, irow7942, rows7951]
  all_goals rfl

theorem atot7942 : totK PD2M8K2 D2M8K2.u7942 = [0, 0, 219637430294, 666480093206, 677940518240, 189330079075, 11819130176, 0] := by
  rw [show D2M8K2.u7942 = KTree.node D2M8K2.t7950 (nat_lit 17179544) (nat_lit 2821574432) (nat_lit 0) D2M8K2.t7951 from rfl, totK_node, tot7950, tot7951]
  decide +kernel

theorem arows7946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7946 = true := by
  rw [show D2M8K2.u7946 = KTree.node D2M8K2.t7952 (nat_lit 17181480) (nat_lit 3424999657) (nat_lit 0) D2M8K2.t7953 from rfl, allE_node, rows7952, irow7946, rows7953]
  all_goals rfl

theorem atot7946 : totK PD2M8K2 D2M8K2.u7946 = [0, 0, 153088622316, 793808177854, 718654450858, 85917637832, 1198073392, 0] := by
  rw [show D2M8K2.u7946 = KTree.node D2M8K2.t7952 (nat_lit 17181480) (nat_lit 3424999657) (nat_lit 0) D2M8K2.t7953 from rfl, totK_node, tot7952, tot7953]
  decide +kernel

theorem arows7947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7947 = true := by
  rw [show D2M8K2.u7947 = KTree.node D2M8K2.t7954 (nat_lit 17183812) (nat_lit 3836880707) (nat_lit 0) D2M8K2.t7955 from rfl, allE_node, rows7954, irow7947, rows7955]
  all_goals rfl

theorem atot7947 : totK PD2M8K2 D2M8K2.u7947 = [0, 0, 341200268459, 898767036727, 482312929998, 32002814914, 0, 0] := by
  rw [show D2M8K2.u7947 = KTree.node D2M8K2.t7954 (nat_lit 17183812) (nat_lit 3836880707) (nat_lit 0) D2M8K2.t7955 from rfl, totK_node, tot7954, tot7955]
  decide +kernel

theorem arows7949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7949 = true := by
  rw [show D2M8K2.u7949 = KTree.node D2M8K2.t7956 (nat_lit 17185348) (nat_lit 3741908596) (nat_lit 0) D2M8K2.t7957 from rfl, allE_node, rows7956, irow7949, rows7957]
  all_goals rfl

theorem atot7949 : totK PD2M8K2 D2M8K2.u7949 = [0, 0, 77540919046, 617911440631, 883930855008, 183981299489, 4980514959, 0] := by
  rw [show D2M8K2.u7949 = KTree.node D2M8K2.t7956 (nat_lit 17185348) (nat_lit 3741908596) (nat_lit 0) D2M8K2.t7957 from rfl, totK_node, tot7956, tot7957]
  decide +kernel

theorem arows7950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7950 = true := by
  rw [show D2M8K2.u7950 = KTree.node D2M8K2.t7958 (nat_lit 17187660) (nat_lit 3059392102) (nat_lit 0) D2M8K2.t7959 from rfl, allE_node, rows7958, irow7950, rows7959]
  all_goals rfl

theorem atot7950 : totK PD2M8K2 D2M8K2.u7950 = [0, 0, 320694522193, 908772229115, 507358523566, 49412928678, 1268739303, 0] := by
  rw [show D2M8K2.u7950 = KTree.node D2M8K2.t7958 (nat_lit 17187660) (nat_lit 3059392102) (nat_lit 0) D2M8K2.t7959 from rfl, totK_node, tot7958, tot7959]
  decide +kernel

theorem arows7953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7953 = true := by
  rw [show D2M8K2.u7953 = KTree.node D2M8K2.t7960 (nat_lit 17190299) (nat_lit 2736986086) (nat_lit 0) D2M8K2.t7961 from rfl, allE_node, rows7960, irow7953, rows7961]
  all_goals rfl

theorem atot7953 : totK PD2M8K2 D2M8K2.u7953 = [0, 0, 0, 489380033433, 976924850356, 275953569982, 10738855752, 0] := by
  rw [show D2M8K2.u7953 = KTree.node D2M8K2.t7960 (nat_lit 17190299) (nat_lit 2736986086) (nat_lit 0) D2M8K2.t7961 from rfl, totK_node, tot7960, tot7961]
  decide +kernel

theorem arows7954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7954 = true := by
  rw [show D2M8K2.u7954 = KTree.node D2M8K2.t7962 (nat_lit 17191971) (nat_lit 1929879276) (nat_lit 0) D2M8K2.t7963 from rfl, allE_node, rows7962, irow7954, rows7963]
  all_goals rfl

theorem atot7954 : totK PD2M8K2 D2M8K2.u7954 = [0, 0, 0, 171635282599, 806422393290, 625779332602, 73987252394, 1209030869] := by
  rw [show D2M8K2.u7954 = KTree.node D2M8K2.t7962 (nat_lit 17191971) (nat_lit 1929879276) (nat_lit 0) D2M8K2.t7963 from rfl, totK_node, tot7962, tot7963]
  decide +kernel

theorem arows7956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7956 = true := by
  rw [show D2M8K2.u7956 = KTree.node D2M8K2.t7964 (nat_lit 17197832) (nat_lit 3634870933) (nat_lit 0) D2M8K2.t7965 from rfl, allE_node, rows7964, irow7956, rows7965]
  all_goals rfl

theorem atot7956 : totK PD2M8K2 D2M8K2.u7956 = [0, 0, 0, 471161258078, 967526227942, 310537714901, 13546714812, 0] := by
  rw [show D2M8K2.u7956 = KTree.node D2M8K2.t7964 (nat_lit 17197832) (nat_lit 3634870933) (nat_lit 0) D2M8K2.t7965 from rfl, totK_node, tot7964, tot7965]
  decide +kernel

theorem arows7957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7957 = true := by
  rw [show D2M8K2.u7957 = KTree.node D2M8K2.t7966 (nat_lit 17201957) (nat_lit 1671111136) (nat_lit 0) D2M8K2.t7967 from rfl, allE_node, rows7966, irow7957, rows7967]
  all_goals rfl

theorem atot7957 : totK PD2M8K2 D2M8K2.u7957 = [0, 0, 0, 485660085076, 991635186980, 267998924961, 5219850835, 0] := by
  rw [show D2M8K2.u7957 = KTree.node D2M8K2.t7966 (nat_lit 17201957) (nat_lit 1671111136) (nat_lit 0) D2M8K2.t7967 from rfl, totK_node, tot7966, tot7967]
  decide +kernel

theorem arows7962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7962 = true := by
  rw [show D2M8K2.u7962 = KTree.node D2M8K2.t7968 (nat_lit 17205214) (nat_lit 2763095335) (nat_lit 0) D2M8K2.t7969 from rfl, allE_node, rows7968, irow7962, rows7969]
  all_goals rfl

theorem atot7962 : totK PD2M8K2 D2M8K2.u7962 = [0, 0, 0, 426647291888, 974275279454, 326847249992, 14662721225, 0] := by
  rw [show D2M8K2.u7962 = KTree.node D2M8K2.t7968 (nat_lit 17205214) (nat_lit 2763095335) (nat_lit 0) D2M8K2.t7969 from rfl, totK_node, tot7968, tot7969]
  decide +kernel

theorem arows7963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7963 = true := by
  rw [show D2M8K2.u7963 = KTree.node D2M8K2.t7970 (nat_lit 17214965) (nat_lit 2401362874) (nat_lit 0) D2M8K2.t7971 from rfl, allE_node, rows7970, irow7963, rows7971]
  all_goals rfl

theorem atot7963 : totK PD2M8K2 D2M8K2.u7963 = [0, 0, 333771904467, 885615036222, 579683280331, 51473007331, 0, 0] := by
  rw [show D2M8K2.u7963 = KTree.node D2M8K2.t7970 (nat_lit 17214965) (nat_lit 2401362874) (nat_lit 0) D2M8K2.t7971 from rfl, totK_node, tot7970, tot7971]
  decide +kernel

theorem arows7965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7965 = true := by
  rw [show D2M8K2.u7965 = KTree.node D2M8K2.t7972 (nat_lit 17216488) (nat_lit 3760342535) (nat_lit 0) D2M8K2.t7973 from rfl, allE_node, rows7972, irow7965, rows7973]
  all_goals rfl

theorem atot7965 : totK PD2M8K2 D2M8K2.u7965 = [0, 0, 106105830409, 663745618787, 820907724439, 242855713534, 13908735795, 0] := by
  rw [show D2M8K2.u7965 = KTree.node D2M8K2.t7972 (nat_lit 17216488) (nat_lit 3760342535) (nat_lit 0) D2M8K2.t7973 from rfl, totK_node, tot7972, tot7973]
  decide +kernel

theorem arows7966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7966 = true := by
  rw [show D2M8K2.u7966 = KTree.node D2M8K2.t7974 (nat_lit 17218181) (nat_lit 2316387304) (nat_lit 0) D2M8K2.t7975 from rfl, allE_node, rows7974, irow7966, rows7975]
  all_goals rfl

theorem atot7966 : totK PD2M8K2 D2M8K2.u7966 = [0, 0, 301903284411, 820894247001, 608583748563, 107141456805, 1409560813, 0] := by
  rw [show D2M8K2.u7966 = KTree.node D2M8K2.t7974 (nat_lit 17218181) (nat_lit 2316387304) (nat_lit 0) D2M8K2.t7975 from rfl, totK_node, tot7974, tot7975]
  decide +kernel

theorem arows7969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7969 = true := by
  rw [show D2M8K2.u7969 = KTree.node D2M8K2.t7976 (nat_lit 17219851) (nat_lit 1356178539) (nat_lit 128) D2M8K2.t7977 from rfl, allE_node, rows7976, irow7969, rows7977]
  all_goals rfl

theorem atot7969 : totK PD2M8K2 D2M8K2.u7969 = [0, 0, 113177815050, 687985104181, 830874960938, 168207019547, 7273823680, 0] := by
  rw [show D2M8K2.u7969 = KTree.node D2M8K2.t7976 (nat_lit 17219851) (nat_lit 1356178539) (nat_lit 128) D2M8K2.t7977 from rfl, totK_node, tot7976, tot7977]
  decide +kernel

theorem arows7970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7970 = true := by
  rw [show D2M8K2.u7970 = KTree.node D2M8K2.t7978 (nat_lit 17222124) (nat_lit 3520604024) (nat_lit 0) D2M8K2.t7979 from rfl, allE_node, rows7978, irow7970, rows7979]
  all_goals rfl

theorem atot7970 : totK PD2M8K2 D2M8K2.u7970 = [0, 0, 363998394376, 876227028262, 515362842477, 75105491173, 2478123692, 0] := by
  rw [show D2M8K2.u7970 = KTree.node D2M8K2.t7978 (nat_lit 17222124) (nat_lit 3520604024) (nat_lit 0) D2M8K2.t7979 from rfl, totK_node, tot7978, tot7979]
  decide +kernel

theorem arows7972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7972 = true := by
  rw [show D2M8K2.u7972 = KTree.node D2M8K2.t7980 (nat_lit 17225310) (nat_lit 3279599504) (nat_lit 0) D2M8K2.t7981 from rfl, allE_node, rows7980, irow7972, rows7981]
  all_goals rfl

theorem atot7972 : totK PD2M8K2 D2M8K2.u7972 = [0, 0, 385008719460, 921408994764, 462058214101, 37135596355, 0, 0] := by
  rw [show D2M8K2.u7972 = KTree.node D2M8K2.t7980 (nat_lit 17225310) (nat_lit 3279599504) (nat_lit 0) D2M8K2.t7981 from rfl, totK_node, tot7980, tot7981]
  decide +kernel

theorem arows7973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7973 = true := by
  rw [show D2M8K2.u7973 = KTree.node D2M8K2.t7982 (nat_lit 17227109) (nat_lit 2343298695) (nat_lit 0) D2M8K2.t7983 from rfl, allE_node, rows7982, irow7973, rows7983]
  all_goals rfl

theorem atot7973 : totK PD2M8K2 D2M8K2.u7973 = [0, 0, 138245867605, 720954161484, 811508048903, 143981660729, 2813333534, 0] := by
  rw [show D2M8K2.u7973 = KTree.node D2M8K2.t7982 (nat_lit 17227109) (nat_lit 2343298695) (nat_lit 0) D2M8K2.t7983 from rfl, totK_node, tot7982, tot7983]
  decide +kernel

theorem arows7977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7977 = true := by
  rw [show D2M8K2.u7977 = KTree.node D2M8K2.t7984 (nat_lit 17229657) (nat_lit 1360855397) (nat_lit 0) D2M8K2.t7985 from rfl, allE_node, rows7984, irow7977, rows7985]
  all_goals rfl

theorem atot7977 : totK PD2M8K2 D2M8K2.u7977 = [0, 0, 401415379968, 972407371684, 455291976565, 35442852580, 0, 0] := by
  rw [show D2M8K2.u7977 = KTree.node D2M8K2.t7984 (nat_lit 17229657) (nat_lit 1360855397) (nat_lit 0) D2M8K2.t7985 from rfl, totK_node, tot7984, tot7985]
  decide +kernel

theorem arows7978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7978 = true := by
  rw [show D2M8K2.u7978 = KTree.node D2M8K2.t7986 (nat_lit 17253720) (nat_lit 3370920733) (nat_lit 0) D2M8K2.t7987 from rfl, allE_node, rows7986, irow7978, rows7987]
  all_goals rfl

theorem atot7978 : totK PD2M8K2 D2M8K2.u7978 = [0, 0, 245015002056, 789748180888, 607940957266, 89676091366, 1310166938, 0] := by
  rw [show D2M8K2.u7978 = KTree.node D2M8K2.t7986 (nat_lit 17253720) (nat_lit 3370920733) (nat_lit 0) D2M8K2.t7987 from rfl, totK_node, tot7986, tot7987]
  decide +kernel

theorem arows7980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7980 = true := by
  rw [show D2M8K2.u7980 = KTree.node D2M8K2.t7988 (nat_lit 17256166) (nat_lit 3778483261) (nat_lit 0) D2M8K2.t7989 from rfl, allE_node, rows7988, irow7980, rows7989]
  all_goals rfl

theorem atot7980 : totK PD2M8K2 D2M8K2.u7980 = [0, 0, 213667333143, 797692257787, 733408737297, 74469475982, 0, 0] := by
  rw [show D2M8K2.u7980 = KTree.node D2M8K2.t7988 (nat_lit 17256166) (nat_lit 3778483261) (nat_lit 0) D2M8K2.t7989 from rfl, totK_node, tot7988, tot7989]
  decide +kernel

theorem arows7981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7981 = true := by
  rw [show D2M8K2.u7981 = KTree.node D2M8K2.t7990 (nat_lit 17257457) (nat_lit 1579302274) (nat_lit 0) D2M8K2.t7991 from rfl, allE_node, rows7990, irow7981, rows7991]
  all_goals rfl

theorem atot7981 : totK PD2M8K2 D2M8K2.u7981 = [0, 0, 197678044991, 704496462351, 691138537282, 213441580768, 13604428459, 0] := by
  rw [show D2M8K2.u7981 = KTree.node D2M8K2.t7990 (nat_lit 17257457) (nat_lit 1579302274) (nat_lit 0) D2M8K2.t7991 from rfl, totK_node, tot7990, tot7991]
  decide +kernel

theorem arows7984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7984 = true := by
  rw [show D2M8K2.u7984 = KTree.node D2M8K2.t7992 (nat_lit 17259380) (nat_lit 3645777265) (nat_lit 0) D2M8K2.t7993 from rfl, allE_node, rows7992, irow7984, rows7993]
  all_goals rfl

theorem atot7984 : totK PD2M8K2 D2M8K2.u7984 = [0, 0, 256031366706, 799350646239, 657621022307, 121131528266, 1409560813, 0] := by
  rw [show D2M8K2.u7984 = KTree.node D2M8K2.t7992 (nat_lit 17259380) (nat_lit 3645777265) (nat_lit 0) D2M8K2.t7993 from rfl, totK_node, tot7992, tot7993]
  decide +kernel

theorem arows7985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7985 = true := by
  rw [show D2M8K2.u7985 = KTree.node D2M8K2.t7994 (nat_lit 17260855) (nat_lit 1285039582) (nat_lit 0) D2M8K2.t7995 from rfl, allE_node, rows7994, irow7985, rows7995]
  all_goals rfl

theorem atot7985 : totK PD2M8K2 D2M8K2.u7985 = [0, 0, 179395172564, 772310443161, 734048188642, 114117294143, 1164319620, 0] := by
  rw [show D2M8K2.u7985 = KTree.node D2M8K2.t7994 (nat_lit 17260855) (nat_lit 1285039582) (nat_lit 0) D2M8K2.t7995 from rfl, totK_node, tot7994, tot7995]
  decide +kernel

theorem arows7987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7987 = true := by
  rw [show D2M8K2.u7987 = KTree.node D2M8K2.t7996 (nat_lit 17262554) (nat_lit 4059953137) (nat_lit 0) D2M8K2.t7997 from rfl, allE_node, rows7996, irow7987, rows7997]
  all_goals rfl

theorem atot7987 : totK PD2M8K2 D2M8K2.u7987 = [0, 0, 169727365698, 648187696980, 737876927483, 208244894392, 11885407614, 0] := by
  rw [show D2M8K2.u7987 = KTree.node D2M8K2.t7996 (nat_lit 17262554) (nat_lit 4059953137) (nat_lit 0) D2M8K2.t7997 from rfl, totK_node, tot7996, tot7997]
  decide +kernel

theorem arows7988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7988 = true := by
  rw [show D2M8K2.u7988 = KTree.node D2M8K2.t7998 (nat_lit 17267374) (nat_lit 3237719296) (nat_lit 0) D2M8K2.t7999 from rfl, allE_node, rows7998, irow7988, rows7999]
  all_goals rfl

theorem atot7988 : totK PD2M8K2 D2M8K2.u7988 = [0, 0, 248977969792, 794680619887, 634443882108, 88209290792, 1096505104, 0] := by
  rw [show D2M8K2.u7988 = KTree.node D2M8K2.t7998 (nat_lit 17267374) (nat_lit 3237719296) (nat_lit 0) D2M8K2.t7999 from rfl, totK_node, tot7998, tot7999]
  decide +kernel

theorem arows7994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7994 = true := by
  rw [show D2M8K2.u7994 = KTree.node D2M8K2.t8000 (nat_lit 17269682) (nat_lit 3314525233) (nat_lit 0) D2M8K2.t8001 from rfl, allE_node, rows8000, irow7994, rows8001]
  all_goals rfl

theorem atot7994 : totK PD2M8K2 D2M8K2.u7994 = [0, 0, 223806669281, 750931088213, 701258854680, 131083098744, 3884009855, 0] := by
  rw [show D2M8K2.u7994 = KTree.node D2M8K2.t8000 (nat_lit 17269682) (nat_lit 3314525233) (nat_lit 0) D2M8K2.t8001 from rfl, totK_node, tot8000, tot8001]
  decide +kernel

theorem arows7995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7995 = true := by
  rw [show D2M8K2.u7995 = KTree.node D2M8K2.t8002 (nat_lit 17271486) (nat_lit 3516729955) (nat_lit 0) D2M8K2.t8003 from rfl, allE_node, rows8002, irow7995, rows8003]
  all_goals rfl

theorem atot7995 : totK PD2M8K2 D2M8K2.u7995 = [0, 0, 119442139608, 672475654445, 819112791074, 178282764039, 4880895167, 0] := by
  rw [show D2M8K2.u7995 = KTree.node D2M8K2.t8002 (nat_lit 17271486) (nat_lit 3516729955) (nat_lit 0) D2M8K2.t8003 from rfl, totK_node, tot8002, tot8003]
  decide +kernel

theorem arows7997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7997 = true := by
  rw [show D2M8K2.u7997 = KTree.node D2M8K2.t8004 (nat_lit 17294771) (nat_lit 2856913723) (nat_lit 0) D2M8K2.t8005 from rfl, allE_node, rows8004, irow7997, rows8005]
  all_goals rfl

theorem atot7997 : totK PD2M8K2 D2M8K2.u7997 = [0, 0, 394198768217, 957862712950, 403250459098, 22319469289, 0, 0] := by
  rw [show D2M8K2.u7997 = KTree.node D2M8K2.t8004 (nat_lit 17294771) (nat_lit 2856913723) (nat_lit 0) D2M8K2.t8005 from rfl, totK_node, tot8004, tot8005]
  decide +kernel

theorem arows7998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7998 = true := by
  rw [show D2M8K2.u7998 = KTree.node D2M8K2.t8006 (nat_lit 17296730) (nat_lit 4037498548) (nat_lit 0) D2M8K2.t8007 from rfl, allE_node, rows8006, irow7998, rows8007]
  all_goals rfl

theorem atot7998 : totK PD2M8K2 D2M8K2.u7998 = [0, 0, 128999756440, 743915208547, 815643803439, 100725136462, 1310517177, 0] := by
  rw [show D2M8K2.u7998 = KTree.node D2M8K2.t8006 (nat_lit 17296730) (nat_lit 4037498548) (nat_lit 0) D2M8K2.t8007 from rfl, totK_node, tot8006, tot8007]
  decide +kernel

theorem arows8001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8001 = true := by
  rw [show D2M8K2.u8001 = KTree.node D2M8K2.t8008 (nat_lit 17298758) (nat_lit 4151327674) (nat_lit 0) D2M8K2.t8009 from rfl, allE_node, rows8008, irow8001, rows8009]
  all_goals rfl

theorem atot8001 : totK PD2M8K2 D2M8K2.u8001 = [0, 0, 446474060238, 990071734055, 386716295995, 22639990811, 0, 0] := by
  rw [show D2M8K2.u8001 = KTree.node D2M8K2.t8008 (nat_lit 17298758) (nat_lit 4151327674) (nat_lit 0) D2M8K2.t8009 from rfl, totK_node, tot8008, tot8009]
  decide +kernel

theorem arows8002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8002 = true := by
  rw [show D2M8K2.u8002 = KTree.node D2M8K2.t8010 (nat_lit 17305592) (nat_lit 3924363918) (nat_lit 0) D2M8K2.t8011 from rfl, allE_node, rows8010, irow8002, rows8011]
  all_goals rfl

theorem atot8002 : totK PD2M8K2 D2M8K2.u8002 = [0, 0, 386079543147, 934131434674, 452080100468, 23212183590, 0, 0] := by
  rw [show D2M8K2.u8002 = KTree.node D2M8K2.t8010 (nat_lit 17305592) (nat_lit 3924363918) (nat_lit 0) D2M8K2.t8011 from rfl, totK_node, tot8010, tot8011]
  decide +kernel

theorem arows8004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8004 = true := by
  rw [show D2M8K2.u8004 = KTree.node D2M8K2.t8012 (nat_lit 17308646) (nat_lit 3838347236) (nat_lit 0) D2M8K2.t8013 from rfl, allE_node, rows8012, irow8004, rows8013]
  all_goals rfl

theorem atot8004 : totK PD2M8K2 D2M8K2.u8004 = [0, 0, 285868089971, 868595220366, 568984486957, 59583244994, 1096505104, 0] := by
  rw [show D2M8K2.u8004 = KTree.node D2M8K2.t8012 (nat_lit 17308646) (nat_lit 3838347236) (nat_lit 0) D2M8K2.t8013 from rfl, totK_node, tot8012, tot8013]
  decide +kernel

theorem arows8005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8005 = true := by
  rw [show D2M8K2.u8005 = KTree.node D2M8K2.t8014 (nat_lit 17310673) (nat_lit 1454138027) (nat_lit 0) D2M8K2.t8015 from rfl, allE_node, rows8014, irow8005, rows8015]
  all_goals rfl

theorem atot8005 : totK PD2M8K2 D2M8K2.u8005 = [0, 0, 174967428964, 740133388012, 723301490575, 136121534817, 3884009855, 0] := by
  rw [show D2M8K2.u8005 = KTree.node D2M8K2.t8014 (nat_lit 17310673) (nat_lit 1454138027) (nat_lit 0) D2M8K2.t8015 from rfl, totK_node, tot8014, tot8015]
  decide +kernel

theorem arows8009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8009 = true := by
  rw [show D2M8K2.u8009 = KTree.node D2M8K2.t8016 (nat_lit 17336693) (nat_lit 2211537840) (nat_lit 0) D2M8K2.t8017 from rfl, allE_node, rows8016, irow8009, rows8017]
  all_goals rfl

theorem atot8009 : totK PD2M8K2 D2M8K2.u8009 = [0, 0, 231865778740, 769456938273, 623186056152, 94901917505, 1326647619, 0] := by
  rw [show D2M8K2.u8009 = KTree.node D2M8K2.t8016 (nat_lit 17336693) (nat_lit 2211537840) (nat_lit 0) D2M8K2.t8017 from rfl, totK_node, tot8016, tot8017]
  decide +kernel

theorem arows8010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8010 = true := by
  rw [show D2M8K2.u8010 = KTree.node D2M8K2.t8018 (nat_lit 17339162) (nat_lit 4144112085) (nat_lit 0) D2M8K2.t8019 from rfl, allE_node, rows8018, irow8010, rows8019]
  all_goals rfl

theorem atot8010 : totK PD2M8K2 D2M8K2.u8010 = [0, 0, 246202130588, 796507340734, 671820969522, 64923087236, 0, 0] := by
  rw [show D2M8K2.u8010 = KTree.node D2M8K2.t8018 (nat_lit 17339162) (nat_lit 4144112085) (nat_lit 0) D2M8K2.t8019 from rfl, totK_node, tot8018, tot8019]
  decide +kernel

theorem arows8012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8012 = true := by
  rw [show D2M8K2.u8012 = KTree.node D2M8K2.t8020 (nat_lit 17340798) (nat_lit 3923973663) (nat_lit 0) D2M8K2.t8021 from rfl, allE_node, rows8020, irow8012, rows8021]
  all_goals rfl

theorem atot8012 : totK PD2M8K2 D2M8K2.u8012 = [0, 0, 170323481364, 683692223349, 723384513200, 214415582278, 13625832554, 0] := by
  rw [show D2M8K2.u8012 = KTree.node D2M8K2.t8020 (nat_lit 17340798) (nat_lit 3923973663) (nat_lit 0) D2M8K2.t8021 from rfl, totK_node, tot8020, tot8021]
  decide +kernel

theorem arows8013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8013 = true := by
  rw [show D2M8K2.u8013 = KTree.node D2M8K2.t8022 (nat_lit 17342360) (nat_lit 3491782222) (nat_lit 0) D2M8K2.t8023 from rfl, allE_node, rows8022, irow8013, rows8023]
  all_goals rfl

theorem atot8013 : totK PD2M8K2 D2M8K2.u8013 = [0, 0, 261315555100, 800296012605, 633050665607, 114854212931, 1409560813, 0] := by
  rw [show D2M8K2.u8013 = KTree.node D2M8K2.t8022 (nat_lit 17342360) (nat_lit 3491782222) (nat_lit 0) D2M8K2.t8023 from rfl, totK_node, tot8022, tot8023]
  decide +kernel

theorem arows8016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8016 = true := by
  rw [show D2M8K2.u8016 = KTree.node D2M8K2.t8024 (nat_lit 17343924) (nat_lit 2876001930) (nat_lit 0) D2M8K2.t8025 from rfl, allE_node, rows8024, irow8016, rows8025]
  all_goals rfl

theorem atot8016 : totK PD2M8K2 D2M8K2.u8016 = [0, 0, 155674322438, 725564473699, 761571288310, 127908222705, 2240648673, 0] := by
  rw [show D2M8K2.u8016 = KTree.node D2M8K2.t8024 (nat_lit 17343924) (nat_lit 2876001930) (nat_lit 0) D2M8K2.t8025 from rfl, totK_node, tot8024, tot8025]
  decide +kernel

theorem arows8017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8017 = true := by
  rw [show D2M8K2.u8017 = KTree.node D2M8K2.t8026 (nat_lit 17345778) (nat_lit 3407810300) (nat_lit 0) D2M8K2.t8027 from rfl, allE_node, rows8026, irow8017, rows8027]
  all_goals rfl

theorem atot8017 : totK PD2M8K2 D2M8K2.u8017 = [0, 0, 255954617972, 724039094355, 619490442169, 159440656403, 10668617419, 0] := by
  rw [show D2M8K2.u8017 = KTree.node D2M8K2.t8026 (nat_lit 17345778) (nat_lit 3407810300) (nat_lit 0) D2M8K2.t8027 from rfl, totK_node, tot8026, tot8027]
  decide +kernel

theorem arows8019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8019 = true := by
  rw [show D2M8K2.u8019 = KTree.node D2M8K2.t8028 (nat_lit 17347485) (nat_lit 1509294181) (nat_lit 0) D2M8K2.t8029 from rfl, allE_node, rows8028, irow8019, rows8029]
  all_goals rfl

theorem atot8019 : totK PD2M8K2 D2M8K2.u8019 = [0, 0, 139018417576, 727067630867, 784335739655, 113629809018, 1162740214, 0] := by
  rw [show D2M8K2.u8019 = KTree.node D2M8K2.t8028 (nat_lit 17347485) (nat_lit 1509294181) (nat_lit 0) D2M8K2.t8029 from rfl, totK_node, tot8028, tot8029]
  decide +kernel

theorem arows8020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8020 = true := by
  rw [show D2M8K2.u8020 = KTree.node D2M8K2.t8030 (nat_lit 17349590) (nat_lit 4149061068) (nat_lit 0) D2M8K2.t8031 from rfl, allE_node, rows8030, irow8020, rows8031]
  all_goals rfl

theorem atot8020 : totK PD2M8K2 D2M8K2.u8020 = [0, 0, 348507625009, 869959723256, 491585025832, 83427496533, 3581949829, 0] := by
  rw [show D2M8K2.u8020 = KTree.node D2M8K2.t8030 (nat_lit 17349590) (nat_lit 4149061068) (nat_lit 0) D2M8K2.t8031 from rfl, totK_node, tot8030, tot8031]
  decide +kernel

theorem arows8025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8025 = true := by
  rw [show D2M8K2.u8025 = KTree.node D2M8K2.t8032 (nat_lit 17351066) (nat_lit 2832695165) (nat_lit 0) D2M8K2.t8033 from rfl, allE_node, rows8032, irow8025, rows8033]
  all_goals rfl

theorem atot8025 : totK PD2M8K2 D2M8K2.u8025 = [0, 0, 92932490688, 705230336530, 872119258644, 135421779397, 1096505104, 0] := by
  rw [show D2M8K2.u8025 = KTree.node D2M8K2.t8032 (nat_lit 17351066) (nat_lit 2832695165) (nat_lit 0) D2M8K2.t8033 from rfl, totK_node, tot8032, tot8033]
  decide +kernel

theorem arows8026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8026 = true := by
  rw [show D2M8K2.u8026 = KTree.node D2M8K2.t8034 (nat_lit 17356750) (nat_lit 3232890599) (nat_lit 0) D2M8K2.t8035 from rfl, allE_node, rows8034, irow8026, rows8035]
  all_goals rfl

theorem atot8026 : totK PD2M8K2 D2M8K2.u8026 = [0, 0, 0, 376026426599, 967364206983, 364181380202, 15751781630, 0] := by
  rw [show D2M8K2.u8026 = KTree.node D2M8K2.t8034 (nat_lit 17356750) (nat_lit 3232890599) (nat_lit 0) D2M8K2.t8035 from rfl, totK_node, tot8034, tot8035]
  decide +kernel

theorem arows8028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8028 = true := by
  rw [show D2M8K2.u8028 = KTree.node D2M8K2.t8036 (nat_lit 17358642) (nat_lit 2950141696) (nat_lit 8) D2M8K2.t8037 from rfl, allE_node, rows8036, irow8028, rows8037]
  all_goals rfl

theorem atot8028 : totK PD2M8K2 D2M8K2.u8028 = [0, 0, 0, 166328801314, 772004978719, 652800121859, 83514655289, 1138244013] := by
  rw [show D2M8K2.u8028 = KTree.node D2M8K2.t8036 (nat_lit 17358642) (nat_lit 2950141696) (nat_lit 8) D2M8K2.t8037 from rfl, totK_node, tot8036, tot8037]
  decide +kernel

theorem arows8029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8029 = true := by
  rw [show D2M8K2.u8029 = KTree.node D2M8K2.t8038 (nat_lit 17360880) (nat_lit 3290801189) (nat_lit 0) D2M8K2.t8039 from rfl, allE_node, rows8038, irow8029, rows8039]
  all_goals rfl

theorem atot8029 : totK PD2M8K2 D2M8K2.u8029 = [0, 0, 0, 473568986029, 960537781616, 326440010431, 15240341619, 0] := by
  rw [show D2M8K2.u8029 = KTree.node D2M8K2.t8038 (nat_lit 17360880) (nat_lit 3290801189) (nat_lit 0) D2M8K2.t8039 from rfl, totK_node, tot8038, tot8039]
  decide +kernel

theorem arows8032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8032 = true := by
  rw [show D2M8K2.u8032 = KTree.node D2M8K2.t8040 (nat_lit 17364348) (nat_lit 2944155516) (nat_lit 0) D2M8K2.t8041 from rfl, allE_node, rows8040, irow8032, rows8041]
  all_goals rfl

theorem atot8032 : totK PD2M8K2 D2M8K2.u8032 = [0, 0, 0, 467424115063, 956965364031, 324732756345, 14910196960, 0] := by
  rw [show D2M8K2.u8032 = KTree.node D2M8K2.t8040 (nat_lit 17364348) (nat_lit 2944155516) (nat_lit 0) D2M8K2.t8041 from rfl, totK_node, tot8040, tot8041]
  decide +kernel

theorem arows8033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8033 = true := by
  rw [show D2M8K2.u8033 = KTree.node D2M8K2.t8042 (nat_lit 17370081) (nat_lit 1744413445) (nat_lit 0) D2M8K2.t8043 from rfl, allE_node, rows8042, irow8033, rows8043]
  all_goals rfl

theorem atot8033 : totK PD2M8K2 D2M8K2.u8033 = [0, 0, 0, 418516156629, 938155471555, 380718100439, 23237176233, 0] := by
  rw [show D2M8K2.u8033 = KTree.node D2M8K2.t8042 (nat_lit 17370081) (nat_lit 1744413445) (nat_lit 0) D2M8K2.t8043 from rfl, totK_node, tot8042, tot8043]
  decide +kernel

theorem arows8035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8035 = true := by
  rw [show D2M8K2.u8035 = KTree.node D2M8K2.t8044 (nat_lit 17371653) (nat_lit 1502350767) (nat_lit 0) D2M8K2.t8045 from rfl, allE_node, rows8044, irow8035, rows8045]
  all_goals rfl

theorem atot8035 : totK PD2M8K2 D2M8K2.u8035 = [0, 0, 0, 175090235727, 801401718674, 666596072498, 87836157337, 1095107716] := by
  rw [show D2M8K2.u8035 = KTree.node D2M8K2.t8044 (nat_lit 17371653) (nat_lit 1502350767) (nat_lit 0) D2M8K2.t8045 from rfl, totK_node, tot8044, tot8045]
  decide +kernel

theorem arows8036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8036 = true := by
  rw [show D2M8K2.u8036 = KTree.node D2M8K2.t8046 (nat_lit 17418930) (nat_lit 2448194888) (nat_lit 0) D2M8K2.t8047 from rfl, allE_node, rows8046, irow8036, rows8047]
  all_goals rfl

theorem atot8036 : totK PD2M8K2 D2M8K2.u8036 = [0, 344808557977, 782004390955, 332991262658, 71350324452, 166085210842, 70523764811, 3882006667] := by
  rw [show D2M8K2.u8036 = KTree.node D2M8K2.t8046 (nat_lit 17418930) (nat_lit 2448194888) (nat_lit 0) D2M8K2.t8047 from rfl, totK_node, tot8046, tot8047]
  decide +kernel

theorem arows8040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8040 = true := by
  rw [show D2M8K2.u8040 = KTree.node D2M8K2.t8048 (nat_lit 17420119) (nat_lit 2175775974) (nat_lit 0) D2M8K2.t8049 from rfl, allE_node, rows8048, irow8040, rows8049]
  all_goals rfl

theorem atot8040 : totK PD2M8K2 D2M8K2.u8040 = [0, 88680480173, 695177697203, 871219420375, 144161759347, 1369150432, 0, 0] := by
  rw [show D2M8K2.u8040 = KTree.node D2M8K2.t8048 (nat_lit 17420119) (nat_lit 2175775974) (nat_lit 0) D2M8K2.t8049 from rfl, totK_node, tot8048, tot8049]
  decide +kernel

theorem arows8041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8041 = true := by
  rw [show D2M8K2.u8041 = KTree.node D2M8K2.t8050 (nat_lit 17425711) (nat_lit 1696642482) (nat_lit 0) D2M8K2.t8051 from rfl, allE_node, rows8050, irow8041, rows8051]
  all_goals rfl

theorem atot8041 : totK PD2M8K2 D2M8K2.u8041 = [0, 344107540154, 906814003489, 512143109427, 45492443555, 0, 0, 0] := by
  rw [show D2M8K2.u8041 = KTree.node D2M8K2.t8050 (nat_lit 17425711) (nat_lit 1696642482) (nat_lit 0) D2M8K2.t8051 from rfl, totK_node, tot8050, tot8051]
  decide +kernel

theorem arows8043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8043 = true := by
  rw [show D2M8K2.u8043 = KTree.node D2M8K2.t8052 (nat_lit 17427268) (nat_lit 3798767105) (nat_lit 0) D2M8K2.t8053 from rfl, allE_node, rows8052, irow8043, rows8053]
  all_goals rfl

theorem atot8043 : totK PD2M8K2 D2M8K2.u8043 = [0, 70176937105, 533816629049, 879916570047, 279182657335, 13049727234, 0, 0] := by
  rw [show D2M8K2.u8043 = KTree.node D2M8K2.t8052 (nat_lit 17427268) (nat_lit 3798767105) (nat_lit 0) D2M8K2.t8053 from rfl, totK_node, tot8052, tot8053]
  decide +kernel

theorem arows8044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8044 = true := by
  rw [show D2M8K2.u8044 = KTree.node D2M8K2.t8054 (nat_lit 17429166) (nat_lit 3845978438) (nat_lit 0) D2M8K2.t8055 from rfl, allE_node, rows8054, irow8044, rows8055]
  all_goals rfl

theorem atot8044 : totK PD2M8K2 D2M8K2.u8044 = [0, 332370382756, 881929749377, 524383194644, 55195156254, 0, 0, 0] := by
  rw [show D2M8K2.u8044 = KTree.node D2M8K2.t8054 (nat_lit 17429166) (nat_lit 3845978438) (nat_lit 0) D2M8K2.t8055 from rfl, totK_node, tot8054, tot8055]
  decide +kernel

theorem arows8047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8047 = true := by
  rw [show D2M8K2.u8047 = KTree.node D2M8K2.t8056 (nat_lit 17431210) (nat_lit 3866993879) (nat_lit 0) D2M8K2.t8057 from rfl, allE_node, rows8056, irow8047, rows8057]
  all_goals rfl

theorem atot8047 : totK PD2M8K2 D2M8K2.u8047 = [0, 82222247619, 599695373796, 886040860295, 222745527167, 5455647540, 0, 0] := by
  rw [show D2M8K2.u8047 = KTree.node D2M8K2.t8056 (nat_lit 17431210) (nat_lit 3866993879) (nat_lit 0) D2M8K2.t8057 from rfl, totK_node, tot8056, tot8057]
  decide +kernel

theorem arows8048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8048 = true := by
  rw [show D2M8K2.u8048 = KTree.node D2M8K2.t8058 (nat_lit 17433072) (nat_lit 3666280895) (nat_lit 0) D2M8K2.t8059 from rfl, allE_node, rows8058, irow8048, rows8059]
  all_goals rfl

theorem atot8048 : totK PD2M8K2 D2M8K2.u8048 = [0, 287101854686, 852923344237, 551221592343, 70674341420, 1096505104, 0, 0] := by
  rw [show D2M8K2.u8048 = KTree.node D2M8K2.t8058 (nat_lit 17433072) (nat_lit 3666280895) (nat_lit 0) D2M8K2.t8059 from rfl, totK_node, tot8058, tot8059]
  decide +kernel

theorem arows8050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8050 = true := by
  rw [show D2M8K2.u8050 = KTree.node D2M8K2.t8060 (nat_lit 17435595) (nat_lit 2852278665) (nat_lit 0) D2M8K2.t8061 from rfl, allE_node, rows8060, irow8050, rows8061]
  all_goals rfl

theorem atot8050 : totK PD2M8K2 D2M8K2.u8050 = [0, 236509000887, 751815354060, 676729745323, 132664822354, 3884009855, 0, 0] := by
  rw [show D2M8K2.u8050 = KTree.node D2M8K2.t8060 (nat_lit 17435595) (nat_lit 2852278665) (nat_lit 0) D2M8K2.t8061 from rfl, totK_node, tot8060, tot8061]
  decide +kernel

theorem arows8051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8051 = true := by
  rw [show D2M8K2.u8051 = KTree.node D2M8K2.t8062 (nat_lit 17437094) (nat_lit 3982689873) (nat_lit 0) D2M8K2.t8063 from rfl, allE_node, rows8062, irow8051, rows8063]
  all_goals rfl

theorem atot8051 : totK PD2M8K2 D2M8K2.u8051 = [0, 185305993966, 758503241292, 726525176160, 124547834501, 1268739303, 0, 0] := by
  rw [show D2M8K2.u8051 = KTree.node D2M8K2.t8062 (nat_lit 17437094) (nat_lit 3982689873) (nat_lit 0) D2M8K2.t8063 from rfl, totK_node, tot8062, tot8063]
  decide +kernel

theorem arows8058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8058 = true := by
  rw [show D2M8K2.u8058 = KTree.node D2M8K2.t8064 (nat_lit 17438767) (nat_lit 2415566519) (nat_lit 0) D2M8K2.t8065 from rfl, allE_node, rows8064, irow8058, rows8065]
  all_goals rfl

theorem atot8058 : totK PD2M8K2 D2M8K2.u8058 = [0, 0, 388391480298, 961228320108, 404018747966, 22149860293, 0, 0] := by
  rw [show D2M8K2.u8058 = KTree.node D2M8K2.t8064 (nat_lit 17438767) (nat_lit 2415566519) (nat_lit 0) D2M8K2.t8065 from rfl, totK_node, tot8064, tot8065]
  decide +kernel

theorem arows8059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8059 = true := by
  rw [show D2M8K2.u8059 = KTree.node D2M8K2.t8066 (nat_lit 17440279) (nat_lit 2217320037) (nat_lit 0) D2M8K2.t8067 from rfl, allE_node, rows8066, irow8059, rows8067]
  all_goals rfl

theorem atot8059 : totK PD2M8K2 D2M8K2.u8059 = [0, 0, 268126231006, 842216209911, 543651420649, 72882223246, 1369150432, 0] := by
  rw [show D2M8K2.u8059 = KTree.node D2M8K2.t8066 (nat_lit 17440279) (nat_lit 2217320037) (nat_lit 0) D2M8K2.t8067 from rfl, totK_node, tot8066, tot8067]
  decide +kernel

theorem arows8061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8061 = true := by
  rw [show D2M8K2.u8061 = KTree.node D2M8K2.t8068 (nat_lit 17442267) (nat_lit 3007060470) (nat_lit 0) D2M8K2.t8069 from rfl, allE_node, rows8068, irow8061, rows8069]
  all_goals rfl

theorem atot8061 : totK PD2M8K2 D2M8K2.u8061 = [0, 0, 211870388303, 810119336739, 656992727915, 80059973272, 0, 0] := by
  rw [show D2M8K2.u8061 = KTree.node D2M8K2.t8068 (nat_lit 17442267) (nat_lit 3007060470) (nat_lit 0) D2M8K2.t8069 from rfl, totK_node, tot8068, tot8069]
  decide +kernel

theorem arows8062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8062 = true := by
  rw [show D2M8K2.u8062 = KTree.node D2M8K2.t8070 (nat_lit 17447455) (nat_lit 2106461884) (nat_lit 0) D2M8K2.t8071 from rfl, allE_node, rows8070, irow8062, rows8071]
  all_goals rfl

theorem atot8062 : totK PD2M8K2 D2M8K2.u8062 = [0, 0, 356628854483, 942369602291, 455575951744, 23929802207, 0, 0] := by
  rw [show D2M8K2.u8062 = KTree.node D2M8K2.t8070 (nat_lit 17447455) (nat_lit 2106461884) (nat_lit 0) D2M8K2.t8071 from rfl, totK_node, tot8070, tot8071]
  decide +kernel

theorem arows8065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8065 = true := by
  rw [show D2M8K2.u8065 = KTree.node D2M8K2.t8072 (nat_lit 17450910) (nat_lit 3937483510) (nat_lit 0) D2M8K2.t8073 from rfl, allE_node, rows8072, irow8065, rows8073]
  all_goals rfl

theorem atot8065 : totK PD2M8K2 D2M8K2.u8065 = [0, 0, 391486180603, 967795175749, 403337248355, 16678667930, 0, 0] := by
  rw [show D2M8K2.u8065 = KTree.node D2M8K2.t8072 (nat_lit 17450910) (nat_lit 3937483510) (nat_lit 0) D2M8K2.t8073 from rfl, totK_node, tot8072, tot8073]
  decide +kernel

theorem arows8066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8066 = true := by
  rw [show D2M8K2.u8066 = KTree.node D2M8K2.t8074 (nat_lit 17456305) (nat_lit 1511572004) (nat_lit 0) D2M8K2.t8075 from rfl, allE_node, rows8074, irow8066, rows8075]
  all_goals rfl

theorem atot8066 : totK PD2M8K2 D2M8K2.u8066 = [0, 0, 381565605186, 946152390563, 419658362139, 20678961292, 0, 0] := by
  rw [show D2M8K2.u8066 = KTree.node D2M8K2.t8074 (nat_lit 17456305) (nat_lit 1511572004) (nat_lit 0) D2M8K2.t8075 from rfl, totK_node, tot8074, tot8075]
  decide +kernel

theorem arows8068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8068 = true := by
  rw [show D2M8K2.u8068 = KTree.node D2M8K2.t8076 (nat_lit 17457840) (nat_lit 3691976763) (nat_lit 0) D2M8K2.t8077 from rfl, allE_node, rows8076, irow8068, rows8077]
  all_goals rfl

theorem atot8068 : totK PD2M8K2 D2M8K2.u8068 = [0, 164044448628, 536044253059, 765158735240, 342832499072, 21338389516, 0, 0] := by
  rw [show D2M8K2.u8068 = KTree.node D2M8K2.t8076 (nat_lit 17457840) (nat_lit 3691976763) (nat_lit 0) D2M8K2.t8077 from rfl, totK_node, tot8076, tot8077]
  decide +kernel

theorem arows8069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8069 = true := by
  rw [show D2M8K2.u8069 = KTree.node D2M8K2.t8078 (nat_lit 17464424) (nat_lit 3942464715) (nat_lit 0) D2M8K2.t8079 from rfl, allE_node, rows8078, irow8069, rows8079]
  all_goals rfl

theorem atot8069 : totK PD2M8K2 D2M8K2.u8069 = [0, 278842547163, 891709196584, 594734847370, 59920166647, 0, 0, 0] := by
  rw [show D2M8K2.u8069 = KTree.node D2M8K2.t8078 (nat_lit 17464424) (nat_lit 3942464715) (nat_lit 0) D2M8K2.t8079 from rfl, totK_node, tot8078, tot8079]
  decide +kernel

theorem arows8073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8073 = true := by
  rw [show D2M8K2.u8073 = KTree.node D2M8K2.t8080 (nat_lit 17465904) (nat_lit 2205649689) (nat_lit 0) D2M8K2.t8081 from rfl, allE_node, rows8080, irow8073, rows8081]
  all_goals rfl

theorem atot8073 : totK PD2M8K2 D2M8K2.u8073 = [0, 0, 347119125459, 941430272964, 483120179387, 31990431867, 0, 0] := by
  rw [show D2M8K2.u8073 = KTree.node D2M8K2.t8080 (nat_lit 17465904) (nat_lit 2205649689) (nat_lit 0) D2M8K2.t8081 from rfl, totK_node, tot8080, tot8081]
  decide +kernel

theorem arows8074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8074 = true := by
  rw [show D2M8K2.u8074 = KTree.node D2M8K2.t8082 (nat_lit 17467216) (nat_lit 3430010216) (nat_lit 0) D2M8K2.t8083 from rfl, allE_node, rows8082, irow8074, rows8083]
  all_goals rfl

theorem atot8074 : totK PD2M8K2 D2M8K2.u8074 = [0, 367929635872, 899507660774, 476890300075, 75597518856, 5618966238, 0, 0] := by
  rw [show D2M8K2.u8074 = KTree.node D2M8K2.t8082 (nat_lit 17467216) (nat_lit 3430010216) (nat_lit 0) D2M8K2.t8083 from rfl, totK_node, tot8082, tot8083]
  decide +kernel

theorem arows8076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8076 = true := by
  rw [show D2M8K2.u8076 = KTree.node D2M8K2.t8084 (nat_lit 17468932) (nat_lit 3866437580) (nat_lit 0) D2M8K2.t8085 from rfl, allE_node, rows8084, irow8076, rows8085]
  all_goals rfl

theorem atot8076 : totK PD2M8K2 D2M8K2.u8076 = [0, 49223707097, 545854805725, 921255171937, 271095247479, 12032795377, 0, 0] := by
  rw [show D2M8K2.u8076 = KTree.node D2M8K2.t8084 (nat_lit 17468932) (nat_lit 3866437580) (nat_lit 0) D2M8K2.t8085 from rfl, totK_node, tot8084, tot8085]
  decide +kernel

theorem arows8077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8077 = true := by
  rw [show D2M8K2.u8077 = KTree.node D2M8K2.t8086 (nat_lit 17470970) (nat_lit 4226979444) (nat_lit 0) D2M8K2.t8087 from rfl, allE_node, rows8086, irow8077, rows8087]
  all_goals rfl

theorem atot8077 : totK PD2M8K2 D2M8K2.u8077 = [0, 369948394124, 914873669673, 509967857786, 46760442711, 0, 0, 0] := by
  rw [show D2M8K2.u8077 = KTree.node D2M8K2.t8086 (nat_lit 17470970) (nat_lit 4226979444) (nat_lit 0) D2M8K2.t8087 from rfl, totK_node, tot8086, tot8087]
  decide +kernel

theorem arows8080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8080 = true := by
  rw [show D2M8K2.u8080 = KTree.node D2M8K2.t8088 (nat_lit 17472770) (nat_lit 3999014965) (nat_lit 0) D2M8K2.t8089 from rfl, allE_node, rows8088, irow8080, rows8089]
  all_goals rfl

theorem atot8080 : totK PD2M8K2 D2M8K2.u8080 = [0, 53832146393, 546308095116, 928347371901, 271237740221, 9599137095, 0, 0] := by
  rw [show D2M8K2.u8080 = KTree.node D2M8K2.t8088 (nat_lit 17472770) (nat_lit 3999014965) (nat_lit 0) D2M8K2.t8089 from rfl, totK_node, tot8088, tot8089]
  decide +kernel

theorem arows8081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8081 = true := by
  rw [show D2M8K2.u8081 = KTree.node D2M8K2.t8090 (nat_lit 17474492) (nat_lit 3394111771) (nat_lit 0) D2M8K2.t8091 from rfl, allE_node, rows8090, irow8081, rows8091]
  all_goals rfl

theorem atot8081 : totK PD2M8K2 D2M8K2.u8081 = [0, 292111583420, 906586625593, 592976237051, 62223260598, 0, 0, 0] := by
  rw [show D2M8K2.u8081 = KTree.node D2M8K2.t8090 (nat_lit 17474492) (nat_lit 3394111771) (nat_lit 0) D2M8K2.t8091 from rfl, totK_node, tot8090, tot8091]
  decide +kernel

theorem arows8083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8083 = true := by
  rw [show D2M8K2.u8083 = KTree.node D2M8K2.t8092 (nat_lit 17477112) (nat_lit 3610902917) (nat_lit 0) D2M8K2.t8093 from rfl, allE_node, rows8092, irow8083, rows8093]
  all_goals rfl

theorem atot8083 : totK PD2M8K2 D2M8K2.u8083 = [0, 249021254306, 772717771146, 696368379660, 128289331564, 2804045914, 0, 0] := by
  rw [show D2M8K2.u8083 = KTree.node D2M8K2.t8092 (nat_lit 17477112) (nat_lit 3610902917) (nat_lit 0) D2M8K2.t8093 from rfl, totK_node, tot8092, tot8093]
  decide +kernel

theorem arows8084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8084 = true := by
  rw [show D2M8K2.u8084 = KTree.node D2M8K2.t8094 (nat_lit 17478581) (nat_lit 1826497090) (nat_lit 0) D2M8K2.t8095 from rfl, allE_node, rows8094, irow8084, rows8095]
  all_goals rfl

theorem atot8084 : totK PD2M8K2 D2M8K2.u8084 = [0, 178544988679, 756171013054, 738370469435, 129787369733, 1267860612, 0, 0] := by
  rw [show D2M8K2.u8084 = KTree.node D2M8K2.t8094 (nat_lit 17478581) (nat_lit 1826497090) (nat_lit 0) D2M8K2.t8095 from rfl, totK_node, tot8094, tot8095]
  decide +kernel

theorem arows8089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8089 = true := by
  rw [show D2M8K2.u8089 = KTree.node D2M8K2.t8096 (nat_lit 17480283) (nat_lit 3640750391) (nat_lit 0) D2M8K2.t8097 from rfl, allE_node, rows8096, irow8089, rows8097]
  all_goals rfl

theorem atot8089 : totK PD2M8K2 D2M8K2.u8089 = [0, 0, 360396064556, 915741176431, 480325397208, 42836720871, 0, 0] := by
  rw [show D2M8K2.u8089 = KTree.node D2M8K2.t8096 (nat_lit 17480283) (nat_lit 3640750391) (nat_lit 0) D2M8K2.t8097 from rfl, totK_node, tot8096, tot8097]
  decide +kernel

theorem arows8090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8090 = true := by
  rw [show D2M8K2.u8090 = KTree.node D2M8K2.t8098 (nat_lit 17485152) (nat_lit 3054144374) (nat_lit 0) D2M8K2.t8099 from rfl, allE_node, rows8098, irow8090, rows8099]
  all_goals rfl

theorem atot8090 : totK PD2M8K2 D2M8K2.u8090 = [0, 0, 295578211154, 904385162709, 578594972622, 47614991193, 0, 0] := by
  rw [show D2M8K2.u8090 = KTree.node D2M8K2.t8098 (nat_lit 17485152) (nat_lit 3054144374) (nat_lit 0) D2M8K2.t8099 from rfl, totK_node, tot8098, tot8099]
  decide +kernel

theorem arows8092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8092 = true := by
  rw [show D2M8K2.u8092 = KTree.node D2M8K2.t8100 (nat_lit 17486650) (nat_lit 3036972975) (nat_lit 0) D2M8K2.t8101 from rfl, allE_node, rows8100, irow8092, rows8101]
  all_goals rfl

theorem atot8092 : totK PD2M8K2 D2M8K2.u8092 = [0, 0, 0, 339943160138, 931043492422, 473992915279, 30908511316, 0] := by
  rw [show D2M8K2.u8092 = KTree.node D2M8K2.t8100 (nat_lit 17486650) (nat_lit 3036972975) (nat_lit 0) D2M8K2.t8101 from rfl, totK_node, tot8100, tot8101]
  decide +kernel

theorem arows8093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8093 = true := by
  rw [show D2M8K2.u8093 = KTree.node D2M8K2.t8102 (nat_lit 17487984) (nat_lit 3525249791) (nat_lit 0) D2M8K2.t8103 from rfl, allE_node, rows8102, irow8093, rows8103]
  all_goals rfl

theorem atot8093 : totK PD2M8K2 D2M8K2.u8093 = [0, 0, 396707065423, 933752050505, 452661704864, 35139077170, 2106824728, 0] := by
  rw [show D2M8K2.u8093 = KTree.node D2M8K2.t8102 (nat_lit 17487984) (nat_lit 3525249791) (nat_lit 0) D2M8K2.t8103 from rfl, totK_node, tot8102, tot8103]
  decide +kernel

theorem arows8096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8096 = true := by
  rw [show D2M8K2.u8096 = KTree.node D2M8K2.t8104 (nat_lit 17489798) (nat_lit 3904275667) (nat_lit 0) D2M8K2.t8105 from rfl, allE_node, rows8104, irow8096, rows8105]
  all_goals rfl

theorem atot8096 : totK PD2M8K2 D2M8K2.u8096 = [0, 0, 71993481277, 620731002943, 891453232159, 208916541731, 5159868635, 0] := by
  rw [show D2M8K2.u8096 = KTree.node D2M8K2.t8104 (nat_lit 17489798) (nat_lit 3904275667) (nat_lit 0) D2M8K2.t8105 from rfl, totK_node, tot8104, tot8105]
  decide +kernel

theorem arows8097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8097 = true := by
  rw [show D2M8K2.u8097 = KTree.node D2M8K2.t8106 (nat_lit 17491859) (nat_lit 2727601205) (nat_lit 0) D2M8K2.t8107 from rfl, allE_node, rows8106, irow8097, rows8107]
  all_goals rfl

theorem atot8097 : totK PD2M8K2 D2M8K2.u8097 = [0, 0, 332225998788, 919995448345, 536039260043, 43353770249, 0, 0] := by
  rw [show D2M8K2.u8097 = KTree.node D2M8K2.t8106 (nat_lit 17491859) (nat_lit 2727601205) (nat_lit 0) D2M8K2.t8107 from rfl, totK_node, tot8106, tot8107]
  decide +kernel

theorem arows8099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8099 = true := by
  rw [show D2M8K2.u8099 = KTree.node D2M8K2.t8108 (nat_lit 17494034) (nat_lit 3890941901) (nat_lit 0) D2M8K2.t8109 from rfl, allE_node, rows8108, irow8099, rows8109]
  all_goals rfl

theorem atot8099 : totK PD2M8K2 D2M8K2.u8099 = [0, 0, 173240819960, 753536558294, 781927920668, 141591036599, 1557581783, 0] := by
  rw [show D2M8K2.u8099 = KTree.node D2M8K2.t8108 (nat_lit 17494034) (nat_lit 3890941901) (nat_lit 0) D2M8K2.t8109 from rfl, totK_node, tot8108, tot8109]
  decide +kernel

theorem arows8100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8100 = true := by
  rw [show D2M8K2.u8100 = KTree.node D2M8K2.t8110 (nat_lit 17496338) (nat_lit 4106938258) (nat_lit 0) D2M8K2.t8111 from rfl, allE_node, rows8110, irow8100, rows8111]
  all_goals rfl

theorem atot8100 : totK PD2M8K2 D2M8K2.u8100 = [0, 0, 155938437592, 771732243469, 792005085294, 108823852069, 0, 0] := by
  rw [show D2M8K2.u8100 = KTree.node D2M8K2.t8110 (nat_lit 17496338) (nat_lit 4106938258) (nat_lit 0) D2M8K2.t8111 from rfl, totK_node, tot8110, tot8111]
  decide +kernel

theorem arows8104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8104 = true := by
  rw [show D2M8K2.u8104 = KTree.node D2M8K2.t8112 (nat_lit 17498345) (nat_lit 1807873198) (nat_lit 0) D2M8K2.t8113 from rfl, allE_node, rows8112, irow8104, rows8113]
  all_goals rfl

theorem atot8104 : totK PD2M8K2 D2M8K2.u8104 = [0, 0, 387649568911, 924121578265, 468476675898, 43333960613, 1415142070, 0] := by
  rw [show D2M8K2.u8104 = KTree.node D2M8K2.t8112 (nat_lit 17498345) (nat_lit 1807873198) (nat_lit 0) D2M8K2.t8113 from rfl, totK_node, tot8112, tot8113]
  decide +kernel

theorem arows8105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8105 = true := by
  rw [show D2M8K2.u8105 = KTree.node D2M8K2.t8114 (nat_lit 17500153) (nat_lit 1351119979) (nat_lit 0) D2M8K2.t8115 from rfl, allE_node, rows8114, irow8105, rows8115]
  all_goals rfl

theorem atot8105 : totK PD2M8K2 D2M8K2.u8105 = [0, 0, 38096821493, 579004609348, 924230173034, 236995160783, 3622693787, 0] := by
  rw [show D2M8K2.u8105 = KTree.node D2M8K2.t8114 (nat_lit 17500153) (nat_lit 1351119979) (nat_lit 0) D2M8K2.t8115 from rfl, totK_node, tot8114, tot8115]
  decide +kernel

theorem arows8107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8107 = true := by
  rw [show D2M8K2.u8107 = KTree.node D2M8K2.t8116 (nat_lit 17502027) (nat_lit 3294538603) (nat_lit 0) D2M8K2.t8117 from rfl, allE_node, rows8116, irow8107, rows8117]
  all_goals rfl

theorem atot8107 : totK PD2M8K2 D2M8K2.u8107 = [0, 384690482232, 901662355720, 394196655700, 45645868352, 45120833787, 5679676912, 0] := by
  rw [show D2M8K2.u8107 = KTree.node D2M8K2.t8116 (nat_lit 17502027) (nat_lit 3294538603) (nat_lit 0) D2M8K2.t8117 from rfl, totK_node, tot8116, tot8117]
  decide +kernel

theorem arows8108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8108 = true := by
  rw [show D2M8K2.u8108 = KTree.node D2M8K2.t8118 (nat_lit 17503619) (nat_lit 2947981234) (nat_lit 0) D2M8K2.t8119 from rfl, allE_node, rows8118, irow8108, rows8119]
  all_goals rfl

theorem atot8108 : totK PD2M8K2 D2M8K2.u8108 = [0, 116289560245, 680251855180, 856818214641, 148510108335, 1369150432, 0, 0] := by
  rw [show D2M8K2.u8108 = KTree.node D2M8K2.t8118 (nat_lit 17503619) (nat_lit 2947981234) (nat_lit 0) D2M8K2.t8119 from rfl, totK_node, tot8118, tot8119]
  decide +kernel

theorem arows8111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8111 = true := by
  rw [show D2M8K2.u8111 = KTree.node D2M8K2.t8120 (nat_lit 17505679) (nat_lit 2342339542) (nat_lit 0) D2M8K2.t8121 from rfl, allE_node, rows8120, irow8111, rows8121]
  all_goals rfl

theorem atot8111 : totK PD2M8K2 D2M8K2.u8111 = [0, 326416703541, 916238084856, 544980236160, 44486270992, 0, 0, 0] := by
  rw [show D2M8K2.u8111 = KTree.node D2M8K2.t8120 (nat_lit 17505679) (nat_lit 2342339542) (nat_lit 0) D2M8K2.t8121 from rfl, totK_node, tot8120, tot8121]
  decide +kernel

theorem arows8112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8112 = true := by
  rw [show D2M8K2.u8112 = KTree.node D2M8K2.t8122 (nat_lit 17507156) (nat_lit 3050187723) (nat_lit 0) D2M8K2.t8123 from rfl, allE_node, rows8122, irow8112, rows8123]
  all_goals rfl

theorem atot8112 : totK PD2M8K2 D2M8K2.u8112 = [0, 0, 400907819871, 939502808494, 448464449535, 29213440614, 0, 0] := by
  rw [show D2M8K2.u8112 = KTree.node D2M8K2.t8122 (nat_lit 17507156) (nat_lit 3050187723) (nat_lit 0) D2M8K2.t8123 from rfl, totK_node, tot8122, tot8123]
  decide +kernel

theorem arows8114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8114 = true := by
  rw [show D2M8K2.u8114 = KTree.node D2M8K2.t8124 (nat_lit 17508508) (nat_lit 3893739166) (nat_lit 0) D2M8K2.t8125 from rfl, allE_node, rows8124, irow8114, rows8125]
  all_goals rfl

theorem atot8114 : totK PD2M8K2 D2M8K2.u8114 = [0, 333511523330, 815132852276, 541872572207, 132762792834, 6800370819, 0, 0] := by
  rw [show D2M8K2.u8114 = KTree.node D2M8K2.t8124 (nat_lit 17508508) (nat_lit 3893739166) (nat_lit 0) D2M8K2.t8125 from rfl, totK_node, tot8124, tot8125]
  decide +kernel

theorem arows8115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8115 = true := by
  rw [show D2M8K2.u8115 = KTree.node D2M8K2.t8126 (nat_lit 17509960) (nat_lit 3648899999) (nat_lit 0) D2M8K2.t8127 from rfl, allE_node, rows8126, irow8115, rows8127]
  all_goals rfl

theorem atot8115 : totK PD2M8K2 D2M8K2.u8115 = [0, 107725059663, 644921780562, 829516542311, 212281061649, 9587713104, 0, 0] := by
  rw [show D2M8K2.u8115 = KTree.node D2M8K2.t8126 (nat_lit 17509960) (nat_lit 3648899999) (nat_lit 0) D2M8K2.t8127 from rfl, totK_node, tot8126, tot8127]
  decide +kernel

theorem arows8121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8121 = true := by
  rw [show D2M8K2.u8121 = KTree.node D2M8K2.t8128 (nat_lit 17515256) (nat_lit 3862132601) (nat_lit 0) D2M8K2.t8129 from rfl, allE_node, rows8128, irow8121, rows8129]
  all_goals rfl

theorem atot8121 : totK PD2M8K2 D2M8K2.u8121 = [0, 255236610790, 787944213835, 640885192270, 123132846019, 3462014130, 0, 0] := by
  rw [show D2M8K2.u8121 = KTree.node D2M8K2.t8128 (nat_lit 17515256) (nat_lit 3862132601) (nat_lit 0) D2M8K2.t8129 from rfl, totK_node, tot8128, tot8129]
  decide +kernel

theorem arows8122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8122 = true := by
  rw [show D2M8K2.u8122 = KTree.node D2M8K2.t8130 (nat_lit 17517120) (nat_lit 2622465938) (nat_lit 0) D2M8K2.t8131 from rfl, allE_node, rows8130, irow8122, rows8131]
  all_goals rfl

theorem atot8122 : totK PD2M8K2 D2M8K2.u8122 = [0, 154132481590, 663749715229, 788875364895, 176034765232, 4980514959, 0, 0] := by
  rw [show D2M8K2.u8122 = KTree.node D2M8K2.t8130 (nat_lit 17517120) (nat_lit 2622465938) (nat_lit 0) D2M8K2.t8131 from rfl, totK_node, tot8130, tot8131]
  decide +kernel

theorem arows8124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8124 = true := by
  rw [show D2M8K2.u8124 = KTree.node D2M8K2.t8132 (nat_lit 17519167) (nat_lit 1764346693) (nat_lit 0) D2M8K2.t8133 from rfl, allE_node, rows8132, irow8124, rows8133]
  all_goals rfl

theorem atot8124 : totK PD2M8K2 D2M8K2.u8124 = [0, 361722546075, 938710071182, 504222469794, 38148878241, 0, 0, 0] := by
  rw [show D2M8K2.u8124 = KTree.node D2M8K2.t8132 (nat_lit 17519167) (nat_lit 1764346693) (nat_lit 0) D2M8K2.t8133 from rfl, totK_node, tot8132, tot8133]
  decide +kernel

theorem arows8125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8125 = true := by
  rw [show D2M8K2.u8125 = KTree.node D2M8K2.t8134 (nat_lit 17520821) (nat_lit 2401304114) (nat_lit 0) D2M8K2.t8135 from rfl, allE_node, rows8134, irow8125, rows8135]
  all_goals rfl

theorem atot8125 : totK PD2M8K2 D2M8K2.u8125 = [0, 0, 484570474212, 985755366904, 306593506490, 8708200738, 0, 0] := by
  rw [show D2M8K2.u8125 = KTree.node D2M8K2.t8134 (nat_lit 17520821) (nat_lit 2401304114) (nat_lit 0) D2M8K2.t8135 from rfl, totK_node, tot8134, tot8135]
  decide +kernel

theorem arows8128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8128 = true := by
  rw [show D2M8K2.u8128 = KTree.node D2M8K2.t8136 (nat_lit 17522666) (nat_lit 4039820553) (nat_lit 0) D2M8K2.t8137 from rfl, allE_node, rows8136, irow8128, rows8137]
  all_goals rfl

theorem atot8128 : totK PD2M8K2 D2M8K2.u8128 = [0, 0, 353080749306, 928906907538, 441345408686, 28154724041, 0, 0] := by
  rw [show D2M8K2.u8128 = KTree.node D2M8K2.t8136 (nat_lit 17522666) (nat_lit 4039820553) (nat_lit 0) D2M8K2.t8137 from rfl, totK_node, tot8136, tot8137]
  decide +kernel

theorem arows8129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8129 = true := by
  rw [show D2M8K2.u8129 = KTree.node D2M8K2.t8138 (nat_lit 17524329) (nat_lit 1894535000) (nat_lit 0) D2M8K2.t8139 from rfl, allE_node, rows8138, irow8129, rows8139]
  all_goals rfl

theorem atot8129 : totK PD2M8K2 D2M8K2.u8129 = [0, 0, 146904680567, 760808819481, 746837368243, 112443484544, 1206465782, 0] := by
  rw [show D2M8K2.u8129 = KTree.node D2M8K2.t8138 (nat_lit 17524329) (nat_lit 1894535000) (nat_lit 0) D2M8K2.t8139 from rfl, totK_node, tot8138, tot8139]
  decide +kernel

theorem arows8131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8131 = true := by
  rw [show D2M8K2.u8131 = KTree.node D2M8K2.t8140 (nat_lit 17526508) (nat_lit 3101999123) (nat_lit 0) D2M8K2.t8141 from rfl, allE_node, rows8140, irow8131, rows8141]
  all_goals rfl

theorem atot8131 : totK PD2M8K2 D2M8K2.u8131 = [0, 0, 359007214183, 923336427833, 504257331955, 35534802786, 0, 0] := by
  rw [show D2M8K2.u8131 = KTree.node D2M8K2.t8140 (nat_lit 17526508) (nat_lit 3101999123) (nat_lit 0) D2M8K2.t8141 from rfl, totK_node, tot8140, tot8141]
  decide +kernel

theorem arows8132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8132 = true := by
  rw [show D2M8K2.u8132 = KTree.node D2M8K2.t8142 (nat_lit 17529461) (nat_lit 2404007425) (nat_lit 0) D2M8K2.t8143 from rfl, allE_node, rows8142, irow8132, rows8143]
  all_goals rfl

theorem atot8132 : totK PD2M8K2 D2M8K2.u8132 = [0, 0, 383162330359, 949977181555, 448754360888, 28288117611, 0, 0] := by
  rw [show D2M8K2.u8132 = KTree.node D2M8K2.t8142 (nat_lit 17529461) (nat_lit 2404007425) (nat_lit 0) D2M8K2.t8143 from rfl, totK_node, tot8142, tot8143]
  decide +kernel

theorem arows8136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8136 = true := by
  rw [show D2M8K2.u8136 = KTree.node D2M8K2.t8144 (nat_lit 17531164) (nat_lit 3969568137) (nat_lit 0) D2M8K2.t8145 from rfl, allE_node, rows8144, irow8136, rows8145]
  all_goals rfl

theorem atot8136 : totK PD2M8K2 D2M8K2.u8136 = [0, 0, 19433589518, 528572014704, 899486480939, 272503471299, 13016197374, 0] := by
  rw [show D2M8K2.u8136 = KTree.node D2M8K2.t8144 (nat_lit 17531164) (nat_lit 3969568137) (nat_lit 0) D2M8K2.t8145 from rfl, totK_node, tot8144, tot8145]
  decide +kernel

theorem arows8137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8137 = true := by
  rw [show D2M8K2.u8137 = KTree.node D2M8K2.t8146 (nat_lit 17536340) (nat_lit 3232123941) (nat_lit 0) D2M8K2.t8147 from rfl, allE_node, rows8146, irow8137, rows8147]
  all_goals rfl

theorem atot8137 : totK PD2M8K2 D2M8K2.u8137 = [0, 0, 378143389429, 953568862723, 447154588018, 28506831008, 0, 0] := by
  rw [show D2M8K2.u8137 = KTree.node D2M8K2.t8146 (nat_lit 17536340) (nat_lit 3232123941) (nat_lit 0) D2M8K2.t8147 from rfl, totK_node, tot8146, tot8147]
  decide +kernel

theorem arows8139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8139 = true := by
  rw [show D2M8K2.u8139 = KTree.node D2M8K2.t8148 (nat_lit 17539836) (nat_lit 3211026252) (nat_lit 0) D2M8K2.t8149 from rfl, allE_node, rows8148, irow8139, rows8149]
  all_goals rfl

theorem atot8139 : totK PD2M8K2 D2M8K2.u8139 = [0, 0, 386529105291, 947574419178, 452861437592, 30706502172, 0, 0] := by
  rw [show D2M8K2.u8139 = KTree.node D2M8K2.t8148 (nat_lit 17539836) (nat_lit 3211026252) (nat_lit 0) D2M8K2.t8149 from rfl, totK_node, tot8148, tot8149]
  decide +kernel

theorem arows8140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8140 = true := by
  rw [show D2M8K2.u8140 = KTree.node D2M8K2.t8150 (nat_lit 17543446) (nat_lit 2965451745) (nat_lit 0) D2M8K2.t8151 from rfl, allE_node, rows8150, irow8140, rows8151]
  all_goals rfl

theorem atot8140 : totK PD2M8K2 D2M8K2.u8140 = [0, 342231832570, 835972123872, 453373000779, 131386405098, 13566920432, 0, 0] := by
  rw [show D2M8K2.u8140 = KTree.node D2M8K2.t8150 (nat_lit 17543446) (nat_lit 2965451745) (nat_lit 0) D2M8K2.t8151 from rfl, totK_node, tot8150, tot8151]
  decide +kernel

theorem arows8143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8143 = true := by
  rw [show D2M8K2.u8143 = KTree.node D2M8K2.t8152 (nat_lit 17545085) (nat_lit 2298267019) (nat_lit 0) D2M8K2.t8153 from rfl, allE_node, rows8152, irow8143, rows8153]
  all_goals rfl

theorem atot8143 : totK PD2M8K2 D2M8K2.u8143 = [0, 131308362601, 687589571332, 839388372520, 141630314923, 1369150432, 0, 0] := by
  rw [show D2M8K2.u8143 = KTree.node D2M8K2.t8152 (nat_lit 17545085) (nat_lit 2298267019) (nat_lit 0) D2M8K2.t8153 from rfl, totK_node, tot8152, tot8153]
  decide +kernel

theorem arows8144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8144 = true := by
  rw [show D2M8K2.u8144 = KTree.node D2M8K2.t8154 (nat_lit 17547138) (nat_lit 3307154011) (nat_lit 0) D2M8K2.t8155 from rfl, allE_node, rows8154, irow8144, rows8155]
  all_goals rfl

theorem atot8144 : totK PD2M8K2 D2M8K2.u8144 = [0, 323594332678, 922720225020, 545965309708, 44251819613, 0, 0, 0] := by
  rw [show D2M8K2.u8144 = KTree.node D2M8K2.t8154 (nat_lit 17547138) (nat_lit 3307154011) (nat_lit 0) D2M8K2.t8155 from rfl, totK_node, tot8154, tot8155]
  decide +kernel

theorem arows8146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8146 = true := by
  rw [show D2M8K2.u8146 = KTree.node D2M8K2.t8156 (nat_lit 17548734) (nat_lit 3971616199) (nat_lit 0) D2M8K2.t8157 from rfl, allE_node, rows8156, irow8146, rows8157]
  all_goals rfl

theorem atot8146 : totK PD2M8K2 D2M8K2.u8146 = [0, 0, 411256605375, 954382281123, 429464082993, 26856412781, 0, 0] := by
  rw [show D2M8K2.u8146 = KTree.node D2M8K2.t8156 (nat_lit 17548734) (nat_lit 3971616199) (nat_lit 0) D2M8K2.t8157 from rfl, totK_node, tot8156, tot8157]
  decide +kernel

theorem arows8147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8147 = true := by
  rw [show D2M8K2.u8147 = KTree.node D2M8K2.t8158 (nat_lit 17553508) (nat_lit 3290033785) (nat_lit 0) D2M8K2.t8159 from rfl, allE_node, rows8158, irow8147, rows8159]
  all_goals rfl

theorem atot8147 : totK PD2M8K2 D2M8K2.u8147 = [0, 337302155734, 826012296318, 511219598421, 124755033327, 6799735859, 0, 0] := by
  rw [show D2M8K2.u8147 = KTree.node D2M8K2.t8158 (nat_lit 17553508) (nat_lit 3290033785) (nat_lit 0) D2M8K2.t8159 from rfl, totK_node, tot8158, tot8159]
  decide +kernel

theorem arows8152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8152 = true := by
  rw [show D2M8K2.u8152 = KTree.node D2M8K2.t8160 (nat_lit 17555027) (nat_lit 2272311148) (nat_lit 0) D2M8K2.t8161 from rfl, allE_node, rows8160, irow8152, rows8161]
  all_goals rfl

theorem atot8152 : totK PD2M8K2 D2M8K2.u8152 = [0, 89098610365, 597624584807, 868962128171, 233650390938, 9668735432, 0, 0] := by
  rw [show D2M8K2.u8152 = KTree.node D2M8K2.t8160 (nat_lit 17555027) (nat_lit 2272311148) (nat_lit 0) D2M8K2.t8161 from rfl, totK_node, tot8160, tot8161]
  decide +kernel

theorem arows8153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8153 = true := by
  rw [show D2M8K2.u8153 = KTree.node D2M8K2.t8162 (nat_lit 17560309) (nat_lit 1083179563) (nat_lit 0) D2M8K2.t8163 from rfl, allE_node, rows8162, irow8153, rows8163]
  all_goals rfl

theorem atot8153 : totK PD2M8K2 D2M8K2.u8153 = [0, 318812605002, 831212726402, 552750890023, 104551262646, 3581949829, 0, 0] := by
  rw [show D2M8K2.u8153 = KTree.node D2M8K2.t8162 (nat_lit 17560309) (nat_lit 1083179563) (nat_lit 0) D2M8K2.t8163 from rfl, totK_node, tot8162, tot8163]
  decide +kernel

theorem arows8155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8155 = true := by
  rw [show D2M8K2.u8155 = KTree.node D2M8K2.t8164 (nat_lit 17561788) (nat_lit 3754739458) (nat_lit 0) D2M8K2.t8165 from rfl, allE_node, rows8164, irow8155, rows8165]
  all_goals rfl

theorem atot8155 : totK PD2M8K2 D2M8K2.u8155 = [0, 104315706752, 643028447140, 837702977348, 208666240554, 4965269624, 0, 0] := by
  rw [show D2M8K2.u8155 = KTree.node D2M8K2.t8164 (nat_lit 17561788) (nat_lit 3754739458) (nat_lit 0) D2M8K2.t8165 from rfl, totK_node, tot8164, tot8165]
  decide +kernel

theorem arows8156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8156 = true := by
  rw [show D2M8K2.u8156 = KTree.node D2M8K2.t8166 (nat_lit 17563483) (nat_lit 2238932575) (nat_lit 0) D2M8K2.t8167 from rfl, allE_node, rows8166, irow8156, rows8167]
  all_goals rfl

theorem atot8156 : totK PD2M8K2 D2M8K2.u8156 = [0, 0, 375261847673, 965501176896, 413206839346, 20781990054, 0, 0] := by
  rw [show D2M8K2.u8156 = KTree.node D2M8K2.t8166 (nat_lit 17563483) (nat_lit 2238932575) (nat_lit 0) D2M8K2.t8167 from rfl, totK_node, tot8166, tot8167]
  decide +kernel

theorem arows8159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8159 = true := by
  rw [show D2M8K2.u8159 = KTree.node D2M8K2.t8168 (nat_lit 17565184) (nat_lit 3233489627) (nat_lit 0) D2M8K2.t8169 from rfl, allE_node, rows8168, irow8159, rows8169]
  all_goals rfl

theorem atot8159 : totK PD2M8K2 D2M8K2.u8159 = [0, 0, 153126639262, 753784853213, 743023257518, 87773871313, 1239866073, 0] := by
  rw [show D2M8K2.u8159 = KTree.node D2M8K2.t8168 (nat_lit 17565184) (nat_lit 3233489627) (nat_lit 0) D2M8K2.t8169 from rfl, totK_node, tot8168, tot8169]
  decide +kernel

theorem arows8160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8160 = true := by
  rw [show D2M8K2.u8160 = KTree.node D2M8K2.t8170 (nat_lit 17567638) (nat_lit 2900651249) (nat_lit 0) D2M8K2.t8171 from rfl, allE_node, rows8170, irow8160, rows8171]
  all_goals rfl

theorem atot8160 : totK PD2M8K2 D2M8K2.u8160 = [0, 0, 352729063786, 927650100533, 523935573062, 42481037226, 0, 0] := by
  rw [show D2M8K2.u8160 = KTree.node D2M8K2.t8170 (nat_lit 17567638) (nat_lit 2900651249) (nat_lit 0) D2M8K2.t8171 from rfl, totK_node, tot8170, tot8171]
  decide +kernel

theorem arows8162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8162 = true := by
  rw [show D2M8K2.u8162 = KTree.node D2M8K2.t8172 (nat_lit 17574147) (nat_lit 3708139539) (nat_lit 0) D2M8K2.t8173 from rfl, allE_node, rows8172, irow8162, rows8173]
  all_goals rfl

theorem atot8162 : totK PD2M8K2 D2M8K2.u8162 = [0, 0, 370052265655, 918155623748, 486170107866, 39024375868, 0, 0] := by
  rw [show D2M8K2.u8162 = KTree.node D2M8K2.t8172 (nat_lit 17574147) (nat_lit 3708139539) (nat_lit 0) D2M8K2.t8173 from rfl, totK_node, tot8172, tot8173]
  decide +kernel

theorem arows8163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8163 = true := by
  rw [show D2M8K2.u8163 = KTree.node D2M8K2.t8174 (nat_lit 17575636) (nat_lit 2912368292) (nat_lit 0) D2M8K2.t8175 from rfl, allE_node, rows8174, irow8163, rows8175]
  all_goals rfl

theorem atot8163 : totK PD2M8K2 D2M8K2.u8163 = [0, 0, 107070054535, 681696870794, 798244322304, 167505441392, 5425831197, 0] := by
  rw [show D2M8K2.u8163 = KTree.node D2M8K2.t8174 (nat_lit 17575636) (nat_lit 2912368292) (nat_lit 0) D2M8K2.t8175 from rfl, totK_node, tot8174, tot8175]
  decide +kernel

theorem arows8167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8167 = true := by
  rw [show D2M8K2.u8167 = KTree.node D2M8K2.t8176 (nat_lit 17581177) (nat_lit 1177524821) (nat_lit 0) D2M8K2.t8177 from rfl, allE_node, rows8176, irow8167, rows8177]
  all_goals rfl

theorem atot8167 : totK PD2M8K2 D2M8K2.u8167 = [0, 0, 332789443649, 911164533126, 524475736984, 43902047326, 0, 0] := by
  rw [show D2M8K2.u8167 = KTree.node D2M8K2.t8176 (nat_lit 17581177) (nat_lit 1177524821) (nat_lit 0) D2M8K2.t8177 from rfl, totK_node, tot8176, tot8177]
  decide +kernel

theorem arows8168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8168 = true := by
  rw [show D2M8K2.u8168 = KTree.node D2M8K2.t8178 (nat_lit 17626182) (nat_lit 2872924537) (nat_lit 0) D2M8K2.t8179 from rfl, allE_node, rows8178, irow8168, rows8179]
  all_goals rfl

theorem atot8168 : totK PD2M8K2 D2M8K2.u8168 = [0, 277879724131, 784886146006, 558712925154, 162668190887, 13566916688, 0, 0] := by
  rw [show D2M8K2.u8168 = KTree.node D2M8K2.t8178 (nat_lit 17626182) (nat_lit 2872924537) (nat_lit 0) D2M8K2.t8179 from rfl, totK_node, tot8178, tot8179]
  decide +kernel

theorem arows8170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8170 = true := by
  rw [show D2M8K2.u8170 = KTree.node D2M8K2.t8180 (nat_lit 17627431) (nat_lit 2314165833) (nat_lit 0) D2M8K2.t8181 from rfl, allE_node, rows8180, irow8170, rows8181]
  all_goals rfl

theorem atot8170 : totK PD2M8K2 D2M8K2.u8170 = [0, 132604513239, 704130797000, 799036352944, 134391668031, 1369150432, 0, 0] := by
  rw [show D2M8K2.u8170 = KTree.node D2M8K2.t8180 (nat_lit 17627431) (nat_lit 2314165833) (nat_lit 0) D2M8K2.t8181 from rfl, totK_node, tot8180, tot8181]
  decide +kernel

theorem arows8171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8171 = true := by
  rw [show D2M8K2.u8171 = KTree.node D2M8K2.t8182 (nat_lit 17629749) (nat_lit 1599686396) (nat_lit 0) D2M8K2.t8183 from rfl, allE_node, rows8182, irow8171, rows8183]
  all_goals rfl

theorem atot8171 : totK PD2M8K2 D2M8K2.u8171 = [0, 334081105514, 882809702060, 557472758035, 56535045536, 0, 0, 0] := by
  rw [show D2M8K2.u8171 = KTree.node D2M8K2.t8182 (nat_lit 17629749) (nat_lit 1599686396) (nat_lit 0) D2M8K2.t8183 from rfl, totK_node, tot8182, tot8183]
  decide +kernel

theorem arows8174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8174 = true := by
  rw [show D2M8K2.u8174 = KTree.node D2M8K2.t8184 (nat_lit 17631280) (nat_lit 3564630826) (nat_lit 0) D2M8K2.t8185 from rfl, allE_node, rows8184, irow8174, rows8185]
  all_goals rfl

theorem atot8174 : totK PD2M8K2 D2M8K2.u8174 = [0, 90441204705, 546701595778, 820047697873, 338764874279, 26862416910, 0, 0] := by
  rw [show D2M8K2.u8174 = KTree.node D2M8K2.t8184 (nat_lit 17631280) (nat_lit 3564630826) (nat_lit 0) D2M8K2.t8185 from rfl, totK_node, tot8184, tot8185]
  decide +kernel

theorem arows8175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8175 = true := by
  rw [show D2M8K2.u8175 = KTree.node D2M8K2.t8186 (nat_lit 17632576) (nat_lit 3744896351) (nat_lit 0) D2M8K2.t8187 from rfl, allE_node, rows8186, irow8175, rows8187]
  all_goals rfl

theorem atot8175 : totK PD2M8K2 D2M8K2.u8175 = [0, 213292698333, 661518175018, 688774290183, 240483543008, 8204069046, 0, 0] := by
  rw [show D2M8K2.u8175 = KTree.node D2M8K2.t8186 (nat_lit 17632576) (nat_lit 3744896351) (nat_lit 0) D2M8K2.t8187 from rfl, totK_node, tot8186, tot8187]
  decide +kernel

theorem arows8177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8177 = true := by
  rw [show D2M8K2.u8177 = KTree.node D2M8K2.t8188 (nat_lit 17634086) (nat_lit 4005219356) (nat_lit 0) D2M8K2.t8189 from rfl, allE_node, rows8188, irow8177, rows8189]
  all_goals rfl

theorem atot8177 : totK PD2M8K2 D2M8K2.u8177 = [0, 205342374630, 777354420291, 709494537206, 112364960079, 1164319620, 0, 0] := by
  rw [show D2M8K2.u8177 = KTree.node D2M8K2.t8188 (nat_lit 17634086) (nat_lit 4005219356) (nat_lit 0) D2M8K2.t8189 from rfl, totK_node, tot8188, tot8189]
  decide +kernel

theorem arows8178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8178 = true := by
  rw [show D2M8K2.u8178 = KTree.node D2M8K2.t8190 (nat_lit 17635811) (nat_lit 2985155367) (nat_lit 0) D2M8K2.t8191 from rfl, allE_node, rows8190, irow8178, rows8191]
  all_goals rfl

theorem atot8178 : totK PD2M8K2 D2M8K2.u8178 = [0, 170754457897, 657487187856, 745580180247, 204507309781, 9387791372, 0, 0] := by
  rw [show D2M8K2.u8178 = KTree.node D2M8K2.t8190 (nat_lit 17635811) (nat_lit 2985155367) (nat_lit 0) D2M8K2.t8191 from rfl, totK_node, tot8190, tot8191]
  decide +kernel

theorem arows8191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8191 = true := by
  rw [show D2M8K2.u8191 = KTree.node D2M8K2.t8192 (nat_lit 17637530) (nat_lit 4067424481) (nat_lit 0) D2M8K2.t8193 from rfl, allE_node, rows8192, irow8191, rows8193]
  all_goals rfl

theorem atot8191 : totK PD2M8K2 D2M8K2.u8191 = [0, 232269654070, 784088644962, 668892972993, 107579886239, 1198073392, 0, 0] := by
  rw [show D2M8K2.u8191 = KTree.node D2M8K2.t8192 (nat_lit 17637530) (nat_lit 4067424481) (nat_lit 0) D2M8K2.t8193 from rfl, totK_node, tot8192, tot8193]
  decide +kernel

theorem arows8192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8192 = true := by
  rw [show D2M8K2.u8192 = KTree.node D2M8K2.t8194 (nat_lit 17639279) (nat_lit 2777443937) (nat_lit 0) D2M8K2.t8195 from rfl, allE_node, rows8194, irow8192, rows8195]
  all_goals rfl

theorem atot8192 : totK PD2M8K2 D2M8K2.u8192 = [0, 190727951577, 675023337671, 732753929199, 200623067857, 7715358911, 0, 0] := by
  rw [show D2M8K2.u8192 = KTree.node D2M8K2.t8194 (nat_lit 17639279) (nat_lit 2777443937) (nat_lit 0) D2M8K2.t8195 from rfl, totK_node, tot8194, tot8195]
  decide +kernel

theorem arows8194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8194 = true := by
  rw [show D2M8K2.u8194 = KTree.node D2M8K2.t8196 (nat_lit 17644350) (nat_lit 3891323600) (nat_lit 0) D2M8K2.t8197 from rfl, allE_node, rows8196, irow8194, rows8197]
  all_goals rfl

theorem atot8194 : totK PD2M8K2 D2M8K2.u8194 = [0, 252970936551, 810709726657, 650911954142, 112014066426, 1268739303, 0, 0] := by
  rw [show D2M8K2.u8194 = KTree.node D2M8K2.t8196 (nat_lit 17644350) (nat_lit 3891323600) (nat_lit 0) D2M8K2.t8197 from rfl, totK_node, tot8196, tot8197]
  decide +kernel

theorem arows8195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8195 = true := by
  rw [show D2M8K2.u8195 = KTree.node D2M8K2.t8198 (nat_lit 17645702) (nat_lit 2392905832) (nat_lit 0) D2M8K2.t8199 from rfl, allE_node, rows8198, irow8195, rows8199]
  all_goals rfl

theorem atot8195 : totK PD2M8K2 D2M8K2.u8195 = [0, 0, 410753085491, 961332424308, 391009457808, 22149860293, 0, 0] := by
  rw [show D2M8K2.u8195 = KTree.node D2M8K2.t8198 (nat_lit 17645702) (nat_lit 2392905832) (nat_lit 0) D2M8K2.t8199 from rfl, totK_node, tot8198, tot8199]
  decide +kernel

theorem arows8198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8198 = true := by
  rw [show D2M8K2.u8198 = KTree.node D2M8K2.t8200 (nat_lit 17647536) (nat_lit 3539834764) (nat_lit 0) D2M8K2.t8201 from rfl, allE_node, rows8200, irow8198, rows8201]
  all_goals rfl

theorem atot8198 : totK PD2M8K2 D2M8K2.u8198 = [0, 0, 321209797375, 910421358837, 497535243557, 30718220144, 0, 0] := by
  rw [show D2M8K2.u8198 = KTree.node D2M8K2.t8200 (nat_lit 17647536) (nat_lit 3539834764) (nat_lit 0) D2M8K2.t8201 from rfl, totK_node, tot8200, tot8201]
  decide +kernel

theorem arows8199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8199 = true := by
  rw [show D2M8K2.u8199 = KTree.node D2M8K2.t8202 (nat_lit 17649546) (nat_lit 3313168637) (nat_lit 0) D2M8K2.t8203 from rfl, allE_node, rows8202, irow8199, rows8203]
  all_goals rfl

theorem atot8199 : totK PD2M8K2 D2M8K2.u8199 = [0, 0, 179945842210, 706483674839, 781008645085, 122155100238, 1310285577, 0] := by
  rw [show D2M8K2.u8199 = KTree.node D2M8K2.t8202 (nat_lit 17649546) (nat_lit 3313168637) (nat_lit 0) D2M8K2.t8203 from rfl, totK_node, tot8202, tot8203]
  decide +kernel

theorem arows8201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8201 = true := by
  rw [show D2M8K2.u8201 = KTree.node D2M8K2.t8204 (nat_lit 17651192) (nat_lit 3839384042) (nat_lit 0) D2M8K2.t8205 from rfl, allE_node, rows8204, irow8201, rows8205]
  all_goals rfl

theorem atot8201 : totK PD2M8K2 D2M8K2.u8201 = [0, 0, 346694465661, 939625721444, 490999636834, 28114750312, 0, 0] := by
  rw [show D2M8K2.u8201 = KTree.node D2M8K2.t8204 (nat_lit 17651192) (nat_lit 3839384042) (nat_lit 0) D2M8K2.t8205 from rfl, totK_node, tot8204, tot8205]
  decide +kernel

theorem arows8202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8202 = true := by
  rw [show D2M8K2.u8202 = KTree.node D2M8K2.t8206 (nat_lit 17654401) (nat_lit 1540277033) (nat_lit 0) D2M8K2.t8207 from rfl, allE_node, rows8206, irow8202, rows8207]
  all_goals rfl

theorem atot8202 : totK PD2M8K2 D2M8K2.u8202 = [0, 0, 316769424506, 895683506352, 551213437381, 47920080197, 0, 0] := by
  rw [show D2M8K2.u8202 = KTree.node D2M8K2.t8206 (nat_lit 17654401) (nat_lit 1540277033) (nat_lit 0) D2M8K2.t8207 from rfl, totK_node, tot8206, tot8207]
  decide +kernel

theorem arows8206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8206 = true := by
  rw [show D2M8K2.u8206 = KTree.node D2M8K2.t8208 (nat_lit 17656187) (nat_lit 2044443134) (nat_lit 0) D2M8K2.t8209 from rfl, allE_node, rows8208, irow8206, rows8209]
  all_goals rfl

theorem atot8206 : totK PD2M8K2 D2M8K2.u8206 = [0, 0, 169984932980, 685031356846, 735988726594, 162504140294, 4879840392, 0] := by
  rw [show D2M8K2.u8206 = KTree.node D2M8K2.t8208 (nat_lit 17656187) (nat_lit 2044443134) (nat_lit 0) D2M8K2.t8209 from rfl, totK_node, tot8208, tot8209]
  decide +kernel

theorem arows8207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8207 = true := by
  rw [show D2M8K2.u8207 = KTree.node D2M8K2.t8210 (nat_lit 17658030) (nat_lit 3853418972) (nat_lit 0) D2M8K2.t8211 from rfl, allE_node, rows8210, irow8207, rows8211]
  all_goals rfl

theorem atot8207 : totK PD2M8K2 D2M8K2.u8207 = [0, 0, 231049129474, 792935052506, 658248799269, 91880055498, 1107157161, 0] := by
  rw [show D2M8K2.u8207 = KTree.node D2M8K2.t8210 (nat_lit 17658030) (nat_lit 3853418972) (nat_lit 0) D2M8K2.t8211 from rfl, totK_node, tot8210, tot8211]
  decide +kernel

theorem arows8209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8209 = true := by
  rw [show D2M8K2.u8209 = KTree.node D2M8K2.t8212 (nat_lit 17663634) (nat_lit 3382543583) (nat_lit 0) D2M8K2.t8213 from rfl, allE_node, rows8212, irow8209, rows8213]
  all_goals rfl

theorem atot8209 : totK PD2M8K2 D2M8K2.u8209 = [0, 0, 208495613220, 771991240504, 689129946218, 126807557456, 3824247485, 0] := by
  rw [show D2M8K2.u8209 = KTree.node D2M8K2.t8212 (nat_lit 17663634) (nat_lit 3382543583) (nat_lit 0) D2M8K2.t8213 from rfl, totK_node, tot8212, tot8213]
  decide +kernel

theorem arows8210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8210 = true := by
  rw [show D2M8K2.u8210 = KTree.node D2M8K2.t8214 (nat_lit 17665107) (nat_lit 3631486303) (nat_lit 0) D2M8K2.t8215 from rfl, allE_node, rows8214, irow8210, rows8215]
  all_goals rfl

theorem atot8210 : totK PD2M8K2 D2M8K2.u8210 = [0, 0, 232969017420, 801241209840, 664266951019, 103520341462, 1242138600, 0] := by
  rw [show D2M8K2.u8210 = KTree.node D2M8K2.t8214 (nat_lit 17665107) (nat_lit 3631486303) (nat_lit 0) D2M8K2.t8215 from rfl, totK_node, tot8214, tot8215]
  decide +kernel

theorem arows8213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8213 = true := by
  rw [show D2M8K2.u8213 = KTree.node D2M8K2.t8216 (nat_lit 17666816) (nat_lit 2384650015) (nat_lit 0) D2M8K2.t8217 from rfl, allE_node, rows8216, irow8213, rows8217]
  all_goals rfl

theorem atot8213 : totK PD2M8K2 D2M8K2.u8213 = [123894636495, 283213616604, 91833807012, 285769334362, 666456162379, 291561216614, 20509029466, 0] := by
  rw [show D2M8K2.u8213 = KTree.node D2M8K2.t8216 (nat_lit 17666816) (nat_lit 2384650015) (nat_lit 0) D2M8K2.t8217 from rfl, totK_node, tot8216, tot8217]
  decide +kernel

theorem arows8214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8214 = true := by
  rw [show D2M8K2.u8214 = KTree.node D2M8K2.t8218 (nat_lit 17917116) (nat_lit 3182149095) (nat_lit 0) D2M8K2.t8219 from rfl, allE_node, rows8218, irow8214, rows8219]
  all_goals rfl

theorem atot8214 : totK PD2M8K2 D2M8K2.u8214 = [318531460809, 903400705171, 545799894778, 45620042978, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8214 = KTree.node D2M8K2.t8218 (nat_lit 17917116) (nat_lit 3182149095) (nat_lit 0) D2M8K2.t8219 from rfl, totK_node, tot8218, tot8219]
  decide +kernel

theorem arows8216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8216 = true := by
  rw [show D2M8K2.u8216 = KTree.node D2M8K2.t8220 (nat_lit 17918884) (nat_lit 3771248344) (nat_lit 0) D2M8K2.t8221 from rfl, allE_node, rows8220, irow8216, rows8221]
  all_goals rfl

theorem atot8216 : totK PD2M8K2 D2M8K2.u8216 = [139642728415, 717254039068, 821607041642, 136325059023, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u8216 = KTree.node D2M8K2.t8220 (nat_lit 17918884) (nat_lit 3771248344) (nat_lit 0) D2M8K2.t8221 from rfl, totK_node, tot8220, tot8221]
  decide +kernel

theorem arows8217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8217 = true := by
  rw [show D2M8K2.u8217 = KTree.node D2M8K2.t8222 (nat_lit 17924220) (nat_lit 2944155516) (nat_lit 0) D2M8K2.t8223 from rfl, allE_node, rows8222, irow8217, rows8223]
  all_goals rfl

theorem atot8217 : totK PD2M8K2 D2M8K2.u8217 = [260118039086, 789376032648, 620318143767, 96397328944, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u8217 = KTree.node D2M8K2.t8222 (nat_lit 17924220) (nat_lit 2944155516) (nat_lit 0) D2M8K2.t8223 from rfl, totK_node, tot8222, tot8223]
  decide +kernel

theorem arows8222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8222 = true := by
  rw [show D2M8K2.u8222 = KTree.node D2M8K2.t8224 (nat_lit 17925945) (nat_lit 1881068813) (nat_lit 0) D2M8K2.t8225 from rfl, allE_node, rows8224, irow8222, rows8225]
  all_goals rfl

theorem atot8222 : totK PD2M8K2 D2M8K2.u8222 = [156794136647, 637118206951, 746715938664, 223253873276, 11885407614, 0, 0, 0] := by
  rw [show D2M8K2.u8222 = KTree.node D2M8K2.t8224 (nat_lit 17925945) (nat_lit 1881068813) (nat_lit 0) D2M8K2.t8225 from rfl, totK_node, tot8224, tot8225]
  decide +kernel

theorem arows8223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8223 = true := by
  rw [show D2M8K2.u8223 = KTree.node D2M8K2.t8226 (nat_lit 17927603) (nat_lit 1477336312) (nat_lit 0) D2M8K2.t8227 from rfl, allE_node, rows8226, irow8223, rows8227]
  all_goals rfl

theorem atot8223 : totK PD2M8K2 D2M8K2.u8223 = [264572156092, 809932186499, 630512963311, 88365543683, 1198073392, 0, 0, 0] := by
  rw [show D2M8K2.u8223 = KTree.node D2M8K2.t8226 (nat_lit 17927603) (nat_lit 1477336312) (nat_lit 0) D2M8K2.t8227 from rfl, totK_node, tot8226, tot8227]
  decide +kernel

theorem arows8225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8225 = true := by
  rw [show D2M8K2.u8225 = KTree.node D2M8K2.t8228 (nat_lit 17929296) (nat_lit 3591818266) (nat_lit 0) D2M8K2.t8229 from rfl, allE_node, rows8228, irow8225, rows8229]
  all_goals rfl

theorem atot8225 : totK PD2M8K2 D2M8K2.u8225 = [124695669297, 602986408388, 801374557214, 245560914011, 12052611869, 0, 0, 0] := by
  rw [show D2M8K2.u8225 = KTree.node D2M8K2.t8228 (nat_lit 17929296) (nat_lit 3591818266) (nat_lit 0) D2M8K2.t8229 from rfl, totK_node, tot8228, tot8229]
  decide +kernel

theorem arows8226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8226 = true := by
  rw [show D2M8K2.u8226 = KTree.node D2M8K2.t8230 (nat_lit 17930706) (nat_lit 3474668509) (nat_lit 0) D2M8K2.t8231 from rfl, allE_node, rows8230, irow8226, rows8231]
  all_goals rfl

theorem atot8226 : totK PD2M8K2 D2M8K2.u8226 = [289526842416, 867004046322, 568973053376, 51546204894, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8226 = KTree.node D2M8K2.t8230 (nat_lit 17930706) (nat_lit 3474668509) (nat_lit 0) D2M8K2.t8231 from rfl, totK_node, tot8230, tot8231]
  decide +kernel

theorem arows8229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8229 = true := by
  rw [show D2M8K2.u8229 = KTree.node D2M8K2.t8232 (nat_lit 17932666) (nat_lit 2682284768) (nat_lit 0) D2M8K2.t8233 from rfl, allE_node, rows8232, irow8229, rows8233]
  all_goals rfl

theorem atot8229 : totK PD2M8K2 D2M8K2.u8229 = [155727675964, 667669996173, 779985053201, 184075049189, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u8229 = KTree.node D2M8K2.t8232 (nat_lit 17932666) (nat_lit 2682284768) (nat_lit 0) D2M8K2.t8233 from rfl, totK_node, tot8232, tot8233]
  decide +kernel

theorem arows8230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8230 = true := by
  rw [show D2M8K2.u8230 = KTree.node D2M8K2.t8234 (nat_lit 17934219) (nat_lit 3456726686) (nat_lit 0) D2M8K2.t8235 from rfl, allE_node, rows8234, irow8230, rows8235]
  all_goals rfl

theorem atot8230 : totK PD2M8K2 D2M8K2.u8230 = [263514081022, 814624265350, 626350231910, 88330778206, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u8230 = KTree.node D2M8K2.t8234 (nat_lit 17934219) (nat_lit 3456726686) (nat_lit 0) D2M8K2.t8235 from rfl, totK_node, tot8234, tot8235]
  decide +kernel

theorem arows8232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8232 = true := by
  rw [show D2M8K2.u8232 = KTree.node D2M8K2.t8236 (nat_lit 17935898) (nat_lit 3945807289) (nat_lit 0) D2M8K2.t8237 from rfl, allE_node, rows8236, irow8232, rows8237]
  all_goals rfl

theorem atot8232 : totK PD2M8K2 D2M8K2.u8232 = [0, 420983125700, 946000373221, 377138496017, 20780039840, 0, 0, 0] := by
  rw [show D2M8K2.u8232 = KTree.node D2M8K2.t8236 (nat_lit 17935898) (nat_lit 3945807289) (nat_lit 0) D2M8K2.t8237 from rfl, totK_node, tot8236, tot8237]
  decide +kernel

theorem arows8233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8233 = true := by
  rw [show D2M8K2.u8233 = KTree.node D2M8K2.t8238 (nat_lit 17937668) (nat_lit 2853213368) (nat_lit 0) D2M8K2.t8239 from rfl, allE_node, rows8238, irow8233, rows8239]
  all_goals rfl

theorem atot8233 : totK PD2M8K2 D2M8K2.u8233 = [0, 348455622479, 954475829390, 440667131196, 23078955287, 0, 0, 0] := by
  rw [show D2M8K2.u8233 = KTree.node D2M8K2.t8238 (nat_lit 17937668) (nat_lit 2853213368) (nat_lit 0) D2M8K2.t8239 from rfl, totK_node, tot8238, tot8239]
  decide +kernel

theorem arows8237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8237 = true := by
  rw [show D2M8K2.u8237 = KTree.node D2M8K2.t8240 (nat_lit 17939354) (nat_lit 3539516430) (nat_lit 0) D2M8K2.t8241 from rfl, allE_node, rows8240, irow8237, rows8241]
  all_goals rfl

theorem atot8237 : totK PD2M8K2 D2M8K2.u8237 = [0, 105497177992, 698487132064, 793903300174, 142776127880, 1369150432, 0, 0] := by
  rw [show D2M8K2.u8237 = KTree.node D2M8K2.t8240 (nat_lit 17939354) (nat_lit 3539516430) (nat_lit 0) D2M8K2.t8241 from rfl, totK_node, tot8240, tot8241]
  decide +kernel

theorem arows8238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8238 = true := by
  rw [show D2M8K2.u8238 = KTree.node D2M8K2.t8242 (nat_lit 17944806) (nat_lit 3484918013) (nat_lit 0) D2M8K2.t8243 from rfl, allE_node, rows8242, irow8238, rows8243]
  all_goals rfl

theorem atot8238 : totK PD2M8K2 D2M8K2.u8238 = [0, 380699696842, 924143490602, 424728199314, 25145942292, 0, 0, 0] := by
  rw [show D2M8K2.u8238 = KTree.node D2M8K2.t8242 (nat_lit 17944806) (nat_lit 3484918013) (nat_lit 0) D2M8K2.t8243 from rfl, totK_node, tot8242, tot8243]
  decide +kernel

theorem arows8240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8240 = true := by
  rw [show D2M8K2.u8240 = KTree.node D2M8K2.t8244 (nat_lit 17948140) (nat_lit 2978168909) (nat_lit 0) D2M8K2.t8245 from rfl, allE_node, rows8244, irow8240, rows8245]
  all_goals rfl

theorem atot8240 : totK PD2M8K2 D2M8K2.u8240 = [0, 351362135031, 932793120022, 479762115753, 26644587510, 0, 0, 0] := by
  rw [show D2M8K2.u8240 = KTree.node D2M8K2.t8244 (nat_lit 17948140) (nat_lit 2978168909) (nat_lit 0) D2M8K2.t8245 from rfl, totK_node, tot8244, tot8245]
  decide +kernel

theorem arows8241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8241 = true := by
  rw [show D2M8K2.u8241 = KTree.node D2M8K2.t8246 (nat_lit 17951174) (nat_lit 2100254314) (nat_lit 0) D2M8K2.t8247 from rfl, allE_node, rows8246, irow8241, rows8247]
  all_goals rfl

theorem atot8241 : totK PD2M8K2 D2M8K2.u8241 = [0, 394491890763, 949308299285, 397103456794, 19634384088, 0, 0, 0] := by
  rw [show D2M8K2.u8241 = KTree.node D2M8K2.t8246 (nat_lit 17951174) (nat_lit 2100254314) (nat_lit 0) D2M8K2.t8247 from rfl, totK_node, tot8246, tot8247]
  decide +kernel

theorem arows8244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8244 = true := by
  rw [show D2M8K2.u8244 = KTree.node D2M8K2.t8248 (nat_lit 17954488) (nat_lit 3245224274) (nat_lit 0) D2M8K2.t8249 from rfl, allE_node, rows8248, irow8244, rows8249]
  all_goals rfl

theorem atot8244 : totK PD2M8K2 D2M8K2.u8244 = [0, 351448801873, 945434937950, 464443814089, 20161118843, 0, 0, 0] := by
  rw [show D2M8K2.u8244 = KTree.node D2M8K2.t8248 (nat_lit 17954488) (nat_lit 3245224274) (nat_lit 0) D2M8K2.t8249 from rfl, totK_node, tot8248, tot8249]
  decide +kernel

theorem arows8245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8245 = true := by
  rw [show D2M8K2.u8245 = KTree.node D2M8K2.t8250 (nat_lit 17999464) (nat_lit 3886299200) (nat_lit 0) D2M8K2.t8251 from rfl, allE_node, rows8250, irow8245, rows8251]
  all_goals rfl

theorem atot8245 : totK PD2M8K2 D2M8K2.u8245 = [315944076507, 793568515567, 520112152537, 157027406246, 13468148062, 0, 0, 0] := by
  rw [show D2M8K2.u8245 = KTree.node D2M8K2.t8250 (nat_lit 17999464) (nat_lit 3886299200) (nat_lit 0) D2M8K2.t8251 from rfl, totK_node, tot8250, tot8251]
  decide +kernel

theorem arows8247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8247 = true := by
  rw [show D2M8K2.u8247 = KTree.node D2M8K2.t8252 (nat_lit 18000700) (nat_lit 3803260254) (nat_lit 0) D2M8K2.t8253 from rfl, allE_node, rows8252, irow8247, rows8253]
  all_goals rfl

theorem atot8247 : totK PD2M8K2 D2M8K2.u8247 = [104995277616, 702006826514, 842777879049, 140209624198, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u8247 = KTree.node D2M8K2.t8252 (nat_lit 18000700) (nat_lit 3803260254) (nat_lit 0) D2M8K2.t8253 from rfl, totK_node, tot8252, tot8253]
  decide +kernel

theorem arows8248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8248 = true := by
  rw [show D2M8K2.u8248 = KTree.node D2M8K2.t8254 (nat_lit 18006295) (nat_lit 1870528583) (nat_lit 0) D2M8K2.t8255 from rfl, allE_node, rows8254, irow8248, rows8255]
  all_goals rfl

theorem atot8248 : totK PD2M8K2 D2M8K2.u8248 = [338535755071, 910411005217, 518162540815, 47076037007, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8248 = KTree.node D2M8K2.t8254 (nat_lit 18006295) (nat_lit 1870528583) (nat_lit 0) D2M8K2.t8255 from rfl, totK_node, tot8254, tot8255]
  decide +kernel

theorem arows8254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8254 = true := by
  rw [show D2M8K2.u8254 = KTree.node D2M8K2.t8256 (nat_lit 18007817) (nat_lit 1806039617) (nat_lit 0) D2M8K2.t8257 from rfl, allE_node, rows8256, irow8254, rows8257]
  all_goals rfl

theorem atot8254 : totK PD2M8K2 D2M8K2.u8254 = [87070194960, 570059050299, 872720909456, 246656202339, 10568566766, 0, 0, 0] := by
  rw [show D2M8K2.u8254 = KTree.node D2M8K2.t8256 (nat_lit 18007817) (nat_lit 1806039617) (nat_lit 0) D2M8K2.t8257 from rfl, totK_node, tot8256, tot8257]
  decide +kernel

theorem arows8255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8255 = true := by
  rw [show D2M8K2.u8255 = KTree.node D2M8K2.t8258 (nat_lit 18013064) (nat_lit 3911629605) (nat_lit 0) D2M8K2.t8259 from rfl, allE_node, rows8258, irow8255, rows8259]
  all_goals rfl

theorem atot8255 : totK PD2M8K2 D2M8K2.u8255 = [307783738602, 836999789199, 558486297972, 86513917205, 2481160468, 0, 0, 0] := by
  rw [show D2M8K2.u8255 = KTree.node D2M8K2.t8258 (nat_lit 18013064) (nat_lit 3911629605) (nat_lit 0) D2M8K2.t8259 from rfl, totK_node, tot8258, tot8259]
  decide +kernel

theorem arows8257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8257 = true := by
  rw [show D2M8K2.u8257 = KTree.node D2M8K2.t8260 (nat_lit 18014719) (nat_lit 2138727867) (nat_lit 0) D2M8K2.t8261 from rfl, allE_node, rows8260, irow8257, rows8261]
  all_goals rfl

theorem atot8257 : totK PD2M8K2 D2M8K2.u8257 = [90263742309, 657905019635, 863640155945, 166351321524, 2165917952, 0, 0, 0] := by
  rw [show D2M8K2.u8257 = KTree.node D2M8K2.t8260 (nat_lit 18014719) (nat_lit 2138727867) (nat_lit 0) D2M8K2.t8261 from rfl, totK_node, tot8260, tot8261]
  decide +kernel

theorem arows8258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8258 = true := by
  rw [show D2M8K2.u8258 = KTree.node D2M8K2.t8262 (nat_lit 18016711) (nat_lit 1944375160) (nat_lit 0) D2M8K2.t8263 from rfl, allE_node, rows8262, irow8258, rows8263]
  all_goals rfl

theorem atot8258 : totK PD2M8K2 D2M8K2.u8258 = [366338570319, 881812143977, 489796185470, 77391222370, 2814597007, 0, 0, 0] := by
  rw [show D2M8K2.u8258 = KTree.node D2M8K2.t8262 (nat_lit 18016711) (nat_lit 1944375160) (nat_lit 0) D2M8K2.t8263 from rfl, totK_node, tot8262, tot8263]
  decide +kernel

theorem arows8261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8261 = true := by
  rw [show D2M8K2.u8261 = KTree.node D2M8K2.t8264 (nat_lit 18018281) (nat_lit 1594357550) (nat_lit 0) D2M8K2.t8265 from rfl, allE_node, rows8264, irow8261, rows8265]
  all_goals rfl

theorem atot8261 : totK PD2M8K2 D2M8K2.u8261 = [37220374354, 520472789498, 925657480482, 291581723555, 8708200738, 0, 0, 0] := by
  rw [show D2M8K2.u8261 = KTree.node D2M8K2.t8264 (nat_lit 18018281) (nat_lit 1594357550) (nat_lit 0) D2M8K2.t8265 from rfl, totK_node, tot8264, tot8265]
  decide +kernel

theorem arows8262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8262 = true := by
  rw [show D2M8K2.u8262 = KTree.node D2M8K2.t8266 (nat_lit 18020268) (nat_lit 3149788934) (nat_lit 0) D2M8K2.t8267 from rfl, allE_node, rows8266, irow8262, rows8267]
  all_goals rfl

theorem atot8262 : totK PD2M8K2 D2M8K2.u8262 = [0, 369966117233, 942629162195, 428261278919, 25439674165, 0, 0, 0] := by
  rw [show D2M8K2.u8262 = KTree.node D2M8K2.t8266 (nat_lit 18020268) (nat_lit 3149788934) (nat_lit 0) D2M8K2.t8267 from rfl, totK_node, tot8266, tot8267]
  decide +kernel

theorem arows8264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8264 = true := by
  rw [show D2M8K2.u8264 = KTree.node D2M8K2.t8268 (nat_lit 18021586) (nat_lit 3678519383) (nat_lit 0) D2M8K2.t8269 from rfl, allE_node, rows8268, irow8264, rows8269]
  all_goals rfl

theorem atot8264 : totK PD2M8K2 D2M8K2.u8264 = [0, 129659412136, 728902680727, 777712963893, 108089697200, 1206465782, 0, 0] := by
  rw [show D2M8K2.u8264 = KTree.node D2M8K2.t8268 (nat_lit 18021586) (nat_lit 3678519383) (nat_lit 0) D2M8K2.t8269 from rfl, totK_node, tot8268, tot8269]
  decide +kernel

theorem arows8265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8265 = true := by
  rw [show D2M8K2.u8265 = KTree.node D2M8K2.t8270 (nat_lit 18027198) (nat_lit 3105314310) (nat_lit 0) D2M8K2.t8271 from rfl, allE_node, rows8270, irow8265, rows8271]
  all_goals rfl

theorem atot8265 : totK PD2M8K2 D2M8K2.u8265 = [0, 380050807185, 941961833733, 443361445041, 28288117611, 0, 0, 0] := by
  rw [show D2M8K2.u8265 = KTree.node D2M8K2.t8270 (nat_lit 18027198) (nat_lit 3105314310) (nat_lit 0) D2M8K2.t8271 from rfl, totK_node, tot8270, tot8271]
  decide +kernel

theorem arows8269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8269 = true := by
  rw [show D2M8K2.u8269 = KTree.node D2M8K2.t8272 (nat_lit 18028899) (nat_lit 3431558934) (nat_lit 0) D2M8K2.t8273 from rfl, allE_node, rows8272, irow8269, rows8273]
  all_goals rfl

theorem atot8269 : totK PD2M8K2 D2M8K2.u8269 = [0, 7518713851, 492227599315, 929930883756, 280069354355, 13016197374, 0, 0] := by
  rw [show D2M8K2.u8269 = KTree.node D2M8K2.t8272 (nat_lit 18028899) (nat_lit 3431558934) (nat_lit 0) D2M8K2.t8273 from rfl, totK_node, tot8272, tot8273]
  decide +kernel

theorem arows8270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8270 = true := by
  rw [show D2M8K2.u8270 = KTree.node D2M8K2.t8274 (nat_lit 18034085) (nat_lit 2343298695) (nat_lit 0) D2M8K2.t8275 from rfl, allE_node, rows8274, irow8270, rows8275]
  all_goals rfl

theorem atot8270 : totK PD2M8K2 D2M8K2.u8270 = [0, 384858044163, 938790973441, 426395848428, 24200525243, 0, 0, 0] := by
  rw [show D2M8K2.u8270 = KTree.node D2M8K2.t8274 (nat_lit 18034085) (nat_lit 2343298695) (nat_lit 0) D2M8K2.t8275 from rfl, totK_node, tot8274, tot8275]
  decide +kernel

theorem arows8272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8272 = true := by
  rw [show D2M8K2.u8272 = KTree.node D2M8K2.t8276 (nat_lit 18036013) (nat_lit 1091326937) (nat_lit 0) D2M8K2.t8277 from rfl, allE_node, rows8276, irow8272, rows8277]
  all_goals rfl

theorem atot8272 : totK PD2M8K2 D2M8K2.u8272 = [0, 89355778958, 660881759868, 797840465282, 152838964140, 4574395652, 0, 0] := by
  rw [show D2M8K2.u8272 = KTree.node D2M8K2.t8276 (nat_lit 18036013) (nat_lit 1091326937) (nat_lit 0) D2M8K2.t8277 from rfl, totK_node, tot8276, tot8277]
  decide +kernel

theorem arows8273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8273 = true := by
  rw [show D2M8K2.u8273 = KTree.node D2M8K2.t8278 (nat_lit 18037802) (nat_lit 3797428914) (nat_lit 0) D2M8K2.t8279 from rfl, allE_node, rows8278, irow8273, rows8279]
  all_goals rfl

theorem atot8273 : totK PD2M8K2 D2M8K2.u8273 = [72314505312, 412983305492, 824693504491, 465039611559, 41590710221, 0, 0, 0] := by
  rw [show D2M8K2.u8273 = KTree.node D2M8K2.t8278 (nat_lit 18037802) (nat_lit 3797428914) (nat_lit 0) D2M8K2.t8279 from rfl, totK_node, tot8278, tot8279]
  decide +kernel

theorem arows8276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8276 = true := by
  rw [show D2M8K2.u8276 = KTree.node D2M8K2.t8280 (nat_lit 18041402) (nat_lit 3850638624) (nat_lit 0) D2M8K2.t8281 from rfl, allE_node, rows8280, irow8276, rows8281]
  all_goals rfl

theorem atot8276 : totK PD2M8K2 D2M8K2.u8276 = [349188044442, 941786307611, 476358711196, 26278949557, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8276 = KTree.node D2M8K2.t8280 (nat_lit 18041402) (nat_lit 3850638624) (nat_lit 0) D2M8K2.t8281 from rfl, totK_node, tot8280, tot8281]
  decide +kernel

theorem arows8277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8277 = true := by
  rw [show D2M8K2.u8277 = KTree.node D2M8K2.t8282 (nat_lit 18043051) (nat_lit 1599916584) (nat_lit 0) D2M8K2.t8283 from rfl, allE_node, rows8282, irow8277, rows8283]
  all_goals rfl

theorem atot8277 : totK PD2M8K2 D2M8K2.u8277 = [90151632724, 658154501343, 909666126247, 165671022664, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u8277 = KTree.node D2M8K2.t8282 (nat_lit 18043051) (nat_lit 1599916584) (nat_lit 0) D2M8K2.t8283 from rfl, totK_node, tot8282, tot8283]
  decide +kernel

theorem arows8279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8279 = true := by
  rw [show D2M8K2.u8279 = KTree.node D2M8K2.t8284 (nat_lit 18045223) (nat_lit 2296943218) (nat_lit 0) D2M8K2.t8285 from rfl, allE_node, rows8284, irow8279, rows8285]
  all_goals rfl

theorem atot8279 : totK PD2M8K2 D2M8K2.u8279 = [257301217620, 769752463223, 613110362441, 183874042754, 18136157596, 0, 0, 0] := by
  rw [show D2M8K2.u8279 = KTree.node D2M8K2.t8284 (nat_lit 18045223) (nat_lit 2296943218) (nat_lit 0) D2M8K2.t8285 from rfl, totK_node, tot8284, tot8285]
  decide +kernel

theorem arows8280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8280 = true := by
  rw [show D2M8K2.u8280 = KTree.node D2M8K2.t8286 (nat_lit 18046995) (nat_lit 3605230742) (nat_lit 0) D2M8K2.t8287 from rfl, allE_node, rows8286, irow8280, rows8287]
  all_goals rfl

theorem atot8280 : totK PD2M8K2 D2M8K2.u8280 = [168354573532, 591931146156, 750115944033, 296461727213, 15210231259, 0, 0, 0] := by
  rw [show D2M8K2.u8280 = KTree.node D2M8K2.t8286 (nat_lit 18046995) (nat_lit 3605230742) (nat_lit 0) D2M8K2.t8287 from rfl, totK_node, tot8286, tot8287]
  decide +kernel

theorem arows8285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8285 = true := by
  rw [show D2M8K2.u8285 = KTree.node D2M8K2.t8288 (nat_lit 18051934) (nat_lit 3262579029) (nat_lit 0) D2M8K2.t8289 from rfl, allE_node, rows8288, irow8285, rows8289]
  all_goals rfl

theorem atot8285 : totK PD2M8K2 D2M8K2.u8285 = [272659406170, 878730227862, 626014946484, 57659245907, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8285 = KTree.node D2M8K2.t8288 (nat_lit 18051934) (nat_lit 3262579029) (nat_lit 0) D2M8K2.t8289 from rfl, totK_node, tot8288, tot8289]
  decide +kernel

theorem arows8286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8286 = true := by
  rw [show D2M8K2.u8286 = KTree.node D2M8K2.t8290 (nat_lit 18053603) (nat_lit 2051585133) (nat_lit 0) D2M8K2.t8291 from rfl, allE_node, rows8290, irow8286, rows8291]
  all_goals rfl

theorem atot8286 : totK PD2M8K2 D2M8K2.u8286 = [84865244063, 530666650286, 864167804540, 291038786669, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u8286 = KTree.node D2M8K2.t8290 (nat_lit 18053603) (nat_lit 2051585133) (nat_lit 0) D2M8K2.t8291 from rfl, totK_node, tot8290, tot8291]
  decide +kernel

theorem arows8288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8288 = true := by
  rw [show D2M8K2.u8288 = KTree.node D2M8K2.t8292 (nat_lit 18055034) (nat_lit 4211893860) (nat_lit 0) D2M8K2.t8293 from rfl, allE_node, rows8292, irow8288, rows8293]
  all_goals rfl

theorem atot8288 : totK PD2M8K2 D2M8K2.u8288 = [324923473738, 902588682489, 533448405384, 44133070982, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8288 = KTree.node D2M8K2.t8292 (nat_lit 18055034) (nat_lit 4211893860) (nat_lit 0) D2M8K2.t8293 from rfl, totK_node, tot8292, tot8293]
  decide +kernel

theorem arows8289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8289 = true := by
  rw [show D2M8K2.u8289 = KTree.node D2M8K2.t8294 (nat_lit 18056869) (nat_lit 1153827855) (nat_lit 0) D2M8K2.t8295 from rfl, allE_node, rows8294, irow8289, rows8295]
  all_goals rfl

theorem atot8289 : totK PD2M8K2 D2M8K2.u8289 = [118410150176, 631621143205, 838806602901, 197013110125, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u8289 = KTree.node D2M8K2.t8294 (nat_lit 18056869) (nat_lit 1153827855) (nat_lit 0) D2M8K2.t8295 from rfl, totK_node, tot8294, tot8295]
  decide +kernel

theorem arows8292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8292 = true := by
  rw [show D2M8K2.u8292 = KTree.node D2M8K2.t8296 (nat_lit 18058587) (nat_lit 3623267831) (nat_lit 0) D2M8K2.t8297 from rfl, allE_node, rows8296, irow8292, rows8297]
  all_goals rfl

theorem atot8292 : totK PD2M8K2 D2M8K2.u8292 = [296693726884, 881319466540, 597020382046, 56414414563, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8292 = KTree.node D2M8K2.t8296 (nat_lit 18058587) (nat_lit 3623267831) (nat_lit 0) D2M8K2.t8297 from rfl, totK_node, tot8296, tot8297]
  decide +kernel

theorem arows8293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8293 = true := by
  rw [show D2M8K2.u8293 = KTree.node D2M8K2.t8298 (nat_lit 18060285) (nat_lit 1489093300) (nat_lit 0) D2M8K2.t8299 from rfl, allE_node, rows8298, irow8293, rows8299]
  all_goals rfl

theorem atot8293 : totK PD2M8K2 D2M8K2.u8293 = [0, 403947305794, 950859034966, 396956554241, 22042137240, 0, 0, 0] := by
  rw [show D2M8K2.u8293 = KTree.node D2M8K2.t8298 (nat_lit 18060285) (nat_lit 1489093300) (nat_lit 0) D2M8K2.t8299 from rfl, totK_node, tot8298, tot8299]
  decide +kernel

theorem arows8295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8295 = true := by
  rw [show D2M8K2.u8295 = KTree.node D2M8K2.t8300 (nat_lit 18062154) (nat_lit 3721400068) (nat_lit 0) D2M8K2.t8301 from rfl, allE_node, rows8300, irow8295, rows8301]
  all_goals rfl

theorem atot8295 : totK PD2M8K2 D2M8K2.u8295 = [0, 347421458946, 964944172740, 442115565569, 18787744322, 0, 0, 0] := by
  rw [show D2M8K2.u8295 = KTree.node D2M8K2.t8300 (nat_lit 18062154) (nat_lit 3721400068) (nat_lit 0) D2M8K2.t8301 from rfl, totK_node, tot8300, tot8301]
  decide +kernel

theorem arows8296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8296 = true := by
  rw [show D2M8K2.u8296 = KTree.node D2M8K2.t8302 (nat_lit 18063989) (nat_lit 2319331805) (nat_lit 0) D2M8K2.t8303 from rfl, allE_node, rows8302, irow8296, rows8303]
  all_goals rfl

theorem atot8296 : totK PD2M8K2 D2M8K2.u8296 = [0, 127169944728, 696760767393, 834507872285, 126317954546, 1239866073, 0, 0] := by
  rw [show D2M8K2.u8296 = KTree.node D2M8K2.t8302 (nat_lit 18063989) (nat_lit 2319331805) (nat_lit 0) D2M8K2.t8303 from rfl, totK_node, tot8302, tot8303]
  decide +kernel

theorem arows8300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8300 = true := by
  rw [show D2M8K2.u8300 = KTree.node D2M8K2.t8304 (nat_lit 18066073) (nat_lit 1439177058) (nat_lit 0) D2M8K2.t8305 from rfl, allE_node, rows8304, irow8300, rows8305]
  all_goals rfl

theorem atot8300 : totK PD2M8K2 D2M8K2.u8300 = [0, 390778084468, 976710044758, 436529950875, 24084893184, 0, 0, 0] := by
  rw [show D2M8K2.u8300 = KTree.node D2M8K2.t8304 (nat_lit 18066073) (nat_lit 1439177058) (nat_lit 0) D2M8K2.t8305 from rfl, totK_node, tot8304, tot8305]
  decide +kernel

theorem arows8301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8301 = true := by
  rw [show D2M8K2.u8301 = KTree.node D2M8K2.t8306 (nat_lit 18072725) (nat_lit 1525384617) (nat_lit 0) D2M8K2.t8307 from rfl, allE_node, rows8306, irow8301, rows8307]
  all_goals rfl

theorem atot8301 : totK PD2M8K2 D2M8K2.u8301 = [0, 267216708220, 830455173254, 610525970573, 79236614445, 1171084559, 0, 0] := by
  rw [show D2M8K2.u8301 = KTree.node D2M8K2.t8306 (nat_lit 18072725) (nat_lit 1525384617) (nat_lit 0) D2M8K2.t8307 from rfl, totK_node, tot8306, tot8307]
  decide +kernel

theorem arows8303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8303 = true := by
  rw [show D2M8K2.u8303 = KTree.node D2M8K2.t8308 (nat_lit 18074389) (nat_lit 1243102186) (nat_lit 0) D2M8K2.t8309 from rfl, allE_node, rows8308, irow8303, rows8309]
  all_goals rfl

theorem atot8303 : totK PD2M8K2 D2M8K2.u8303 = [0, 112539209047, 593905669565, 795387723837, 238032498371, 11934365838, 0, 0] := by
  rw [show D2M8K2.u8303 = KTree.node D2M8K2.t8308 (nat_lit 18074389) (nat_lit 1243102186) (nat_lit 0) D2M8K2.t8309 from rfl, totK_node, tot8308, tot8309]
  decide +kernel

theorem arows8304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8304 = true := by
  rw [show D2M8K2.u8304 = KTree.node D2M8K2.t8310 (nat_lit 18075887) (nat_lit 2593460602) (nat_lit 0) D2M8K2.t8311 from rfl, allE_node, rows8310, irow8304, rows8311]
  all_goals rfl

theorem atot8304 : totK PD2M8K2 D2M8K2.u8304 = [0, 291662136966, 871454276911, 545412965553, 56524500336, 1053411165, 0, 0] := by
  rw [show D2M8K2.u8304 = KTree.node D2M8K2.t8310 (nat_lit 18075887) (nat_lit 2593460602) (nat_lit 0) D2M8K2.t8311 from rfl, totK_node, tot8310, tot8311]
  decide +kernel

theorem arows8307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8307 = true := by
  rw [show D2M8K2.u8307 = KTree.node D2M8K2.t8312 (nat_lit 18077910) (nat_lit 3299125218) (nat_lit 0) D2M8K2.t8313 from rfl, allE_node, rows8312, irow8307, rows8313]
  all_goals rfl

theorem atot8307 : totK PD2M8K2 D2M8K2.u8307 = [0, 166263517563, 710501146286, 741033502360, 139086439649, 3667207281, 0, 0] := by
  rw [show D2M8K2.u8307 = KTree.node D2M8K2.t8312 (nat_lit 18077910) (nat_lit 3299125218) (nat_lit 0) D2M8K2.t8313 from rfl, totK_node, tot8312, tot8313]
  decide +kernel

theorem arows8308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8308 = true := by
  rw [show D2M8K2.u8308 = KTree.node D2M8K2.t8314 (nat_lit 18079803) (nat_lit 3755335418) (nat_lit 0) D2M8K2.t8315 from rfl, allE_node, rows8314, irow8308, rows8315]
  all_goals rfl

theorem atot8308 : totK PD2M8K2 D2M8K2.u8308 = [121522739692, 513041292325, 750350506992, 396946409230, 31581470956, 0, 0, 0] := by
  rw [show D2M8K2.u8308 = KTree.node D2M8K2.t8314 (nat_lit 18079803) (nat_lit 3755335418) (nat_lit 0) D2M8K2.t8315 from rfl, totK_node, tot8314, tot8315]
  decide +kernel

theorem arows8310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8310 = true := by
  rw [show D2M8K2.u8310 = KTree.node D2M8K2.t8316 (nat_lit 18082995) (nat_lit 3341776524) (nat_lit 0) D2M8K2.t8317 from rfl, allE_node, rows8316, irow8310, rows8317]
  all_goals rfl

theorem atot8310 : totK PD2M8K2 D2M8K2.u8310 = [297275831331, 873003204130, 554915741327, 48371394267, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8310 = KTree.node D2M8K2.t8316 (nat_lit 18082995) (nat_lit 3341776524) (nat_lit 0) D2M8K2.t8317 from rfl, totK_node, tot8316, tot8317]
  decide +kernel

theorem arows8311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8311 = true := by
  rw [show D2M8K2.u8311 = KTree.node D2M8K2.t8318 (nat_lit 18084965) (nat_lit 2268803656) (nat_lit 0) D2M8K2.t8319 from rfl, allE_node, rows8318, irow8311, rows8319]
  all_goals rfl

theorem atot8311 : totK PD2M8K2 D2M8K2.u8311 = [157202694930, 693508000142, 816530843986, 147861758130, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u8311 = KTree.node D2M8K2.t8318 (nat_lit 18084965) (nat_lit 2268803656) (nat_lit 0) D2M8K2.t8319 from rfl, totK_node, tot8318, tot8319]
  decide +kernel

theorem arows8318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8318 = true := by
  rw [show D2M8K2.u8318 = KTree.node D2M8K2.t8320 (nat_lit 18086640) (nat_lit 3290801189) (nat_lit 0) D2M8K2.t8321 from rfl, allE_node, rows8320, irow8318, rows8321]
  all_goals rfl

theorem atot8318 : totK PD2M8K2 D2M8K2.u8318 = [172453763319, 662018286262, 692174654455, 261354998401, 25268263310, 0, 0, 0] := by
  rw [show D2M8K2.u8318 = KTree.node D2M8K2.t8320 (nat_lit 18086640) (nat_lit 3290801189) (nat_lit 0) D2M8K2.t8321 from rfl, totK_node, tot8320, tot8321]
  decide +kernel

theorem arows8319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8319 = true := by
  rw [show D2M8K2.u8319 = KTree.node D2M8K2.t8322 (nat_lit 18088805) (nat_lit 2311029913) (nat_lit 0) D2M8K2.t8323 from rfl, allE_node, rows8322, irow8319, rows8323]
  all_goals rfl

theorem atot8319 : totK PD2M8K2 D2M8K2.u8319 = [239637722811, 695864854146, 668088175024, 200258877008, 5430665091, 0, 0, 0] := by
  rw [show D2M8K2.u8319 = KTree.node D2M8K2.t8322 (nat_lit 18088805) (nat_lit 2311029913) (nat_lit 0) D2M8K2.t8323 from rfl, totK_node, tot8322, tot8323]
  decide +kernel

theorem arows8321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8321 = true := by
  rw [show D2M8K2.u8321 = KTree.node D2M8K2.t8324 (nat_lit 18090454) (nat_lit 3346477076) (nat_lit 0) D2M8K2.t8325 from rfl, allE_node, rows8324, irow8321, rows8325]
  all_goals rfl

theorem atot8321 : totK PD2M8K2 D2M8K2.u8321 = [140377068119, 659963409254, 772093621369, 186663501538, 7166294683, 0, 0, 0] := by
  rw [show D2M8K2.u8321 = KTree.node D2M8K2.t8324 (nat_lit 18090454) (nat_lit 3346477076) (nat_lit 0) D2M8K2.t8325 from rfl, totK_node, tot8324, tot8325]
  decide +kernel

theorem arows8322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8322 = true := by
  rw [show D2M8K2.u8322 = KTree.node D2M8K2.t8326 (nat_lit 18092379) (nat_lit 1709782445) (nat_lit 0) D2M8K2.t8327 from rfl, allE_node, rows8326, irow8322, rows8327]
  all_goals rfl

theorem atot8322 : totK PD2M8K2 D2M8K2.u8322 = [257170070944, 766604684288, 630024981708, 135307007771, 5883432551, 0, 0, 0] := by
  rw [show D2M8K2.u8322 = KTree.node D2M8K2.t8326 (nat_lit 18092379) (nat_lit 1709782445) (nat_lit 0) D2M8K2.t8327 from rfl, totK_node, tot8326, tot8327]
  decide +kernel

theorem arows8325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8325 = true := by
  rw [show D2M8K2.u8325 = KTree.node D2M8K2.t8328 (nat_lit 18093944) (nat_lit 3432696860) (nat_lit 0) D2M8K2.t8329 from rfl, allE_node, rows8328, irow8325, rows8329]
  all_goals rfl

theorem atot8325 : totK PD2M8K2 D2M8K2.u8325 = [156922691767, 688463893315, 771724067554, 177104658307, 3544300177, 0, 0, 0] := by
  rw [show D2M8K2.u8325 = KTree.node D2M8K2.t8328 (nat_lit 18093944) (nat_lit 3432696860) (nat_lit 0) D2M8K2.t8329 from rfl, totK_node, tot8328, tot8329]
  decide +kernel

theorem arows8326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8326 = true := by
  rw [show D2M8K2.u8326 = KTree.node D2M8K2.t8330 (nat_lit 18095753) (nat_lit 1594117532) (nat_lit 0) D2M8K2.t8331 from rfl, allE_node, rows8330, irow8326, rows8331]
  all_goals rfl

theorem atot8326 : totK PD2M8K2 D2M8K2.u8326 = [255235158978, 742274813587, 629526976804, 156756714422, 9706385084, 0, 0, 0] := by
  rw [show D2M8K2.u8326 = KTree.node D2M8K2.t8330 (nat_lit 18095753) (nat_lit 1594117532) (nat_lit 0) D2M8K2.t8331 from rfl, totK_node, tot8330, tot8331]
  decide +kernel

theorem arows8328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8328 = true := by
  rw [show D2M8K2.u8328 = KTree.node D2M8K2.t8332 (nat_lit 18096942) (nat_lit 3833293425) (nat_lit 0) D2M8K2.t8333 from rfl, allE_node, rows8332, irow8328, rows8333]
  all_goals rfl

theorem atot8328 : totK PD2M8K2 D2M8K2.u8328 = [180114736652, 765088731303, 749305084619, 110422712532, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u8328 = KTree.node D2M8K2.t8332 (nat_lit 18096942) (nat_lit 3833293425) (nat_lit 0) D2M8K2.t8333 from rfl, totK_node, tot8332, tot8333]
  decide +kernel

theorem arows8329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8329 = true := by
  rw [show D2M8K2.u8329 = KTree.node D2M8K2.t8334 (nat_lit 18102654) (nat_lit 3762940657) (nat_lit 0) D2M8K2.t8335 from rfl, allE_node, rows8334, irow8329, rows8335]
  all_goals rfl

theorem atot8329 : totK PD2M8K2 D2M8K2.u8329 = [0, 448947170956, 969016937561, 333718412540, 14810258184, 0, 0, 0] := by
  rw [show D2M8K2.u8329 = KTree.node D2M8K2.t8334 (nat_lit 18102654) (nat_lit 3762940657) (nat_lit 0) D2M8K2.t8335 from rfl, totK_node, tot8334, tot8335]
  decide +kernel

theorem arows8333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8333 = true := by
  rw [show D2M8K2.u8333 = KTree.node D2M8K2.t8336 (nat_lit 18104263) (nat_lit 2336870603) (nat_lit 0) D2M8K2.t8337 from rfl, allE_node, rows8336, irow8333, rows8337]
  all_goals rfl

theorem atot8333 : totK PD2M8K2 D2M8K2.u8333 = [0, 157929339591, 778146498693, 701034416051, 91226322929, 1138244013, 0, 0] := by
  rw [show D2M8K2.u8333 = KTree.node D2M8K2.t8336 (nat_lit 18104263) (nat_lit 2336870603) (nat_lit 0) D2M8K2.t8337 from rfl, totK_node, tot8336, tot8337]
  decide +kernel

theorem arows8334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8334 = true := by
  rw [show D2M8K2.u8334 = KTree.node D2M8K2.t8338 (nat_lit 18106734) (nat_lit 3207858262) (nat_lit 0) D2M8K2.t8339 from rfl, allE_node, rows8338, irow8334, rows8339]
  all_goals rfl

theorem atot8334 : totK PD2M8K2 D2M8K2.u8334 = [0, 328905851971, 927434989349, 518441419931, 45306705239, 0, 0, 0] := by
  rw [show D2M8K2.u8334 = KTree.node D2M8K2.t8338 (nat_lit 18106734) (nat_lit 3207858262) (nat_lit 0) D2M8K2.t8339 from rfl, totK_node, tot8338, tot8339]
  decide +kernel

theorem arows8336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8336 = true := by
  rw [show D2M8K2.u8336 = KTree.node D2M8K2.t8340 (nat_lit 18110114) (nat_lit 4014791921) (nat_lit 0) D2M8K2.t8341 from rfl, allE_node, rows8340, irow8336, rows8341]
  all_goals rfl

theorem atot8336 : totK PD2M8K2 D2M8K2.u8336 = [0, 378302871566, 925314561726, 443413497637, 26270157348, 0, 0, 0] := by
  rw [show D2M8K2.u8336 = KTree.node D2M8K2.t8340 (nat_lit 18110114) (nat_lit 4014791921) (nat_lit 0) D2M8K2.t8341 from rfl, totK_node, tot8340, tot8341]
  decide +kernel

theorem arows8337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8337 = true := by
  rw [show D2M8K2.u8337 = KTree.node D2M8K2.t8342 (nat_lit 18113772) (nat_lit 3549511286) (nat_lit 0) D2M8K2.t8343 from rfl, allE_node, rows8342, irow8337, rows8343]
  all_goals rfl

theorem atot8337 : totK PD2M8K2 D2M8K2.u8337 = [0, 375332296770, 941028191613, 457729022411, 26141763735, 0, 0, 0] := by
  rw [show D2M8K2.u8337 = KTree.node D2M8K2.t8342 (nat_lit 18113772) (nat_lit 3549511286) (nat_lit 0) D2M8K2.t8343 from rfl, totK_node, tot8342, tot8343]
  decide +kernel

theorem arows8340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8340 = true := by
  rw [show D2M8K2.u8340 = KTree.node D2M8K2.t8344 (nat_lit 18116813) (nat_lit 2188725635) (nat_lit 0) D2M8K2.t8345 from rfl, allE_node, rows8344, irow8340, rows8345]
  all_goals rfl

theorem atot8340 : totK PD2M8K2 D2M8K2.u8340 = [0, 377465391805, 934943809280, 438846501673, 27914443105, 0, 0, 0] := by
  rw [show D2M8K2.u8340 = KTree.node D2M8K2.t8344 (nat_lit 18116813) (nat_lit 2188725635) (nat_lit 0) D2M8K2.t8345 from rfl, totK_node, tot8344, tot8345]
  decide +kernel

theorem arows8341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8341 = true := by
  rw [show D2M8K2.u8341 = KTree.node D2M8K2.t8346 (nat_lit 18118298) (nat_lit 2429907246) (nat_lit 0) D2M8K2.t8347 from rfl, allE_node, rows8346, irow8341, rows8347]
  all_goals rfl

theorem atot8341 : totK PD2M8K2 D2M8K2.u8341 = [0, 92453491279, 703801654708, 814491582849, 129189168423, 1095107716, 0, 0] := by
  rw [show D2M8K2.u8341 = KTree.node D2M8K2.t8346 (nat_lit 18118298) (nat_lit 2429907246) (nat_lit 0) D2M8K2.t8347 from rfl, totK_node, tot8346, tot8347]
  decide +kernel

theorem arows8343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8343 = true := by
  rw [show D2M8K2.u8343 = KTree.node D2M8K2.t8348 (nat_lit 18124006) (nat_lit 2465141117) (nat_lit 0) D2M8K2.t8349 from rfl, allE_node, rows8348, irow8343, rows8349]
  all_goals rfl

theorem atot8343 : totK PD2M8K2 D2M8K2.u8343 = [330004772267, 836188003225, 392714548354, 131905627295, 71452959291, 3882006667, 0, 0] := by
  rw [show D2M8K2.u8343 = KTree.node D2M8K2.t8348 (nat_lit 18124006) (nat_lit 2465141117) (nat_lit 0) D2M8K2.t8349 from rfl, totK_node, tot8348, tot8349]
  decide +kernel

theorem arows8344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8344 = true := by
  rw [show D2M8K2.u8344 = KTree.node D2M8K2.t8350 (nat_lit 18125577) (nat_lit 1780164845) (nat_lit 0) D2M8K2.t8351 from rfl, allE_node, rows8350, irow8344, rows8351]
  all_goals rfl

theorem atot8344 : totK PD2M8K2 D2M8K2.u8344 = [109310888610, 659713675628, 886728643512, 157549061266, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u8344 = KTree.node D2M8K2.t8350 (nat_lit 18125577) (nat_lit 1780164845) (nat_lit 0) D2M8K2.t8351 from rfl, totK_node, tot8350, tot8351]
  decide +kernel

theorem arows8349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8349 = true := by
  rw [show D2M8K2.u8349 = KTree.node D2M8K2.t8352 (nat_lit 18127662) (nat_lit 4079301544) (nat_lit 0) D2M8K2.t8353 from rfl, allE_node, rows8352, irow8349, rows8353]
  all_goals rfl

theorem atot8349 : totK PD2M8K2 D2M8K2.u8349 = [312984341803, 898275230199, 577887483384, 64284121802, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8349 = KTree.node D2M8K2.t8352 (nat_lit 18127662) (nat_lit 4079301544) (nat_lit 0) D2M8K2.t8353 from rfl, totK_node, tot8352, tot8353]
  decide +kernel

theorem arows8350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8350 = true := by
  rw [show D2M8K2.u8350 = KTree.node D2M8K2.t8354 (nat_lit 18129449) (nat_lit 1089001684) (nat_lit 0) D2M8K2.t8355 from rfl, allE_node, rows8354, irow8350, rows8355]
  all_goals rfl

theorem atot8350 : totK PD2M8K2 D2M8K2.u8350 = [84333515894, 439807852879, 823869695825, 428310629681, 34863985312, 0, 0, 0] := by
  rw [show D2M8K2.u8350 = KTree.node D2M8K2.t8354 (nat_lit 18129449) (nat_lit 1089001684) (nat_lit 0) D2M8K2.t8355 from rfl, totK_node, tot8354, tot8355]
  decide +kernel

theorem arows8352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8352 = true := by
  rw [show D2M8K2.u8352 = KTree.node D2M8K2.t8356 (nat_lit 18131023) (nat_lit 1571948895) (nat_lit 0) D2M8K2.t8357 from rfl, allE_node, rows8356, irow8352, rows8357]
  all_goals rfl

theorem atot8352 : totK PD2M8K2 D2M8K2.u8352 = [297440569189, 881158919591, 574069355184, 53744487703, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8352 = KTree.node D2M8K2.t8356 (nat_lit 18131023) (nat_lit 1571948895) (nat_lit 0) D2M8K2.t8357 from rfl, totK_node, tot8356, tot8357]
  decide +kernel

theorem arows8353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8353 = true := by
  rw [show D2M8K2.u8353 = KTree.node D2M8K2.t8358 (nat_lit 18133117) (nat_lit 1203439621) (nat_lit 0) D2M8K2.t8359 from rfl, allE_node, rows8358, irow8353, rows8359]
  all_goals rfl

theorem atot8353 : totK PD2M8K2 D2M8K2.u8353 = [115759888752, 576859885051, 803389961632, 262952335515, 13043783340, 0, 0, 0] := by
  rw [show D2M8K2.u8353 = KTree.node D2M8K2.t8358 (nat_lit 18133117) (nat_lit 1203439621) (nat_lit 0) D2M8K2.t8359 from rfl, totK_node, tot8358, tot8359]
  decide +kernel

theorem arows8356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8356 = true := by
  rw [show D2M8K2.u8356 = KTree.node D2M8K2.t8360 (nat_lit 18134831) (nat_lit 1934562260) (nat_lit 0) D2M8K2.t8361 from rfl, allE_node, rows8360, irow8356, rows8361]
  all_goals rfl

theorem atot8356 : totK PD2M8K2 D2M8K2.u8356 = [299522665010, 880777665718, 591844347132, 56634434701, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8356 = KTree.node D2M8K2.t8360 (nat_lit 18134831) (nat_lit 1934562260) (nat_lit 0) D2M8K2.t8361 from rfl, totK_node, tot8360, tot8361]
  decide +kernel

theorem arows8357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8357 = true := by
  rw [show D2M8K2.u8357 = KTree.node D2M8K2.t8362 (nat_lit 18136544) (nat_lit 3698238709) (nat_lit 0) D2M8K2.t8363 from rfl, allE_node, rows8362, irow8357, rows8363]
  all_goals rfl

theorem atot8357 : totK PD2M8K2 D2M8K2.u8357 = [87240234242, 553339846806, 849138772621, 285949689804, 13243784863, 0, 0, 0] := by
  rw [show D2M8K2.u8357 = KTree.node D2M8K2.t8362 (nat_lit 18136544) (nat_lit 3698238709) (nat_lit 0) D2M8K2.t8363 from rfl, totK_node, tot8362, tot8363]
  decide +kernel

theorem arows8359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8359 = true := by
  rw [show D2M8K2.u8359 = KTree.node D2M8K2.t8364 (nat_lit 18141409) (nat_lit 1552380795) (nat_lit 0) D2M8K2.t8365 from rfl, allE_node, rows8364, irow8359, rows8365]
  all_goals rfl

theorem atot8359 : totK PD2M8K2 D2M8K2.u8359 = [352470280500, 907252145428, 529540238436, 45827619706, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8359 = KTree.node D2M8K2.t8364 (nat_lit 18141409) (nat_lit 1552380795) (nat_lit 0) D2M8K2.t8365 from rfl, totK_node, tot8364, tot8365]
  decide +kernel

theorem arows8360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8360 = true := by
  rw [show D2M8K2.u8360 = KTree.node D2M8K2.t8366 (nat_lit 18143005) (nat_lit 1035428251) (nat_lit 0) D2M8K2.t8367 from rfl, allE_node, rows8366, irow8360, rows8367]
  all_goals rfl

theorem atot8360 : totK PD2M8K2 D2M8K2.u8360 = [0, 436713883874, 982929452784, 350560616422, 10944102088, 0, 0, 0] := by
  rw [show D2M8K2.u8360 = KTree.node D2M8K2.t8366 (nat_lit 18143005) (nat_lit 1035428251) (nat_lit 0) D2M8K2.t8367 from rfl, totK_node, tot8366, tot8367]
  decide +kernel

theorem arows8364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8364 = true := by
  rw [show D2M8K2.u8364 = KTree.node D2M8K2.t8368 (nat_lit 18144842) (nat_lit 3686282271) (nat_lit 0) D2M8K2.t8369 from rfl, allE_node, rows8368, irow8364, rows8369]
  all_goals rfl

theorem atot8364 : totK PD2M8K2 D2M8K2.u8364 = [0, 383972741732, 951274360420, 414818514489, 20043075046, 0, 0, 0] := by
  rw [show D2M8K2.u8364 = KTree.node D2M8K2.t8368 (nat_lit 18144842) (nat_lit 3686282271) (nat_lit 0) D2M8K2.t8369 from rfl, totK_node, tot8368, tot8369]
  decide +kernel

theorem arows8365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8365 = true := by
  rw [show D2M8K2.u8365 = KTree.node D2M8K2.t8370 (nat_lit 18146435) (nat_lit 2947981234) (nat_lit 0) D2M8K2.t8371 from rfl, allE_node, rows8370, irow8365, rows8371]
  all_goals rfl

theorem atot8365 : totK PD2M8K2 D2M8K2.u8365 = [0, 123464703952, 690782535082, 846765855882, 122151756841, 1310285577, 0, 0] := by
  rw [show D2M8K2.u8365 = KTree.node D2M8K2.t8370 (nat_lit 18146435) (nat_lit 2947981234) (nat_lit 0) D2M8K2.t8371 from rfl, totK_node, tot8370, tot8371]
  decide +kernel

theorem arows8367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8367 = true := by
  rw [show D2M8K2.u8367 = KTree.node D2M8K2.t8372 (nat_lit 18148544) (nat_lit 3456112743) (nat_lit 0) D2M8K2.t8373 from rfl, allE_node, rows8372, irow8367, rows8373]
  all_goals rfl

theorem atot8367 : totK PD2M8K2 D2M8K2.u8367 = [0, 326476876306, 901289937620, 546420026598, 48715501433, 0, 0, 0] := by
  rw [show D2M8K2.u8367 = KTree.node D2M8K2.t8372 (nat_lit 18148544) (nat_lit 3456112743) (nat_lit 0) D2M8K2.t8373 from rfl, totK_node, tot8372, tot8373]
  decide +kernel

theorem arows8368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8368 = true := by
  rw [show D2M8K2.u8368 = KTree.node D2M8K2.t8374 (nat_lit 18152080) (nat_lit 3357963893) (nat_lit 0) D2M8K2.t8375 from rfl, allE_node, rows8374, irow8368, rows8375]
  all_goals rfl

theorem atot8368 : totK PD2M8K2 D2M8K2.u8368 = [0, 296465472502, 867386973605, 573953774315, 51526956833, 0, 0, 0] := by
  rw [show D2M8K2.u8368 = KTree.node D2M8K2.t8374 (nat_lit 18152080) (nat_lit 3357963893) (nat_lit 0) D2M8K2.t8375 from rfl, totK_node, tot8374, tot8375]
  decide +kernel

theorem arows8371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8371 = true := by
  rw [show D2M8K2.u8371 = KTree.node D2M8K2.t8376 (nat_lit 18154109) (nat_lit 2132046136) (nat_lit 0) D2M8K2.t8377 from rfl, allE_node, rows8376, irow8371, rows8377]
  all_goals rfl

theorem atot8371 : totK PD2M8K2 D2M8K2.u8371 = [0, 165808702825, 680436479179, 753416515112, 169515621161, 4879840392, 0, 0] := by
  rw [show D2M8K2.u8371 = KTree.node D2M8K2.t8376 (nat_lit 18154109) (nat_lit 2132046136) (nat_lit 0) D2M8K2.t8377 from rfl, totK_node, tot8376, tot8377]
  decide +kernel

theorem arows8372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8372 = true := by
  rw [show D2M8K2.u8372 = KTree.node D2M8K2.t8378 (nat_lit 18155813) (nat_lit 2047249975) (nat_lit 0) D2M8K2.t8379 from rfl, allE_node, rows8378, irow8372, rows8379]
  all_goals rfl

theorem atot8372 : totK PD2M8K2 D2M8K2.u8372 = [0, 247857554456, 796479714683, 647501993570, 90201183276, 1107157161, 0, 0] := by
  rw [show D2M8K2.u8372 = KTree.node D2M8K2.t8378 (nat_lit 18155813) (nat_lit 2047249975) (nat_lit 0) D2M8K2.t8379 from rfl, totK_node, tot8378, tot8379]
  decide +kernel

theorem arows8374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8374 = true := by
  rw [show D2M8K2.u8374 = KTree.node D2M8K2.t8380 (nat_lit 18161293) (nat_lit 1391339689) (nat_lit 0) D2M8K2.t8381 from rfl, allE_node, rows8380, irow8374, rows8381]
  all_goals rfl

theorem atot8374 : totK PD2M8K2 D2M8K2.u8374 = [0, 206778609456, 754719860470, 700504796190, 132341404500, 3824247485, 0, 0] := by
  rw [show D2M8K2.u8374 = KTree.node D2M8K2.t8380 (nat_lit 18161293) (nat_lit 1391339689) (nat_lit 0) D2M8K2.t8381 from rfl, totK_node, tot8380, tot8381]
  decide +kernel

theorem arows8375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8375 = true := by
  rw [show D2M8K2.u8375 = KTree.node D2M8K2.t8382 (nat_lit 18162778) (nat_lit 4021842791) (nat_lit 0) D2M8K2.t8383 from rfl, allE_node, rows8382, irow8375, rows8383]
  all_goals rfl

theorem atot8375 : totK PD2M8K2 D2M8K2.u8375 = [0, 231322496728, 794453945301, 659432886589, 103520341462, 1242138600, 0, 0] := by
  rw [show D2M8K2.u8375 = KTree.node D2M8K2.t8382 (nat_lit 18162778) (nat_lit 4021842791) (nat_lit 0) D2M8K2.t8383 from rfl, totK_node, tot8382, tot8383]
  decide +kernel

theorem arows8381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8381 = true := by
  rw [show D2M8K2.u8381 = KTree.node D2M8K2.t8384 (nat_lit 18164488) (nat_lit 3671187694) (nat_lit 0) D2M8K2.t8385 from rfl, allE_node, rows8384, irow8381, rows8385]
  all_goals rfl

theorem atot8381 : totK PD2M8K2 D2M8K2.u8381 = [0, 135280300897, 560729093984, 752958719653, 292931037067, 20509029466, 0, 0] := by
  rw [show D2M8K2.u8381 = KTree.node D2M8K2.t8384 (nat_lit 18164488) (nat_lit 3671187694) (nat_lit 0) D2M8K2.t8385 from rfl, totK_node, tot8384, tot8385]
  decide +kernel

theorem arows8382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8382 = true := by
  rw [show D2M8K2.u8382 = KTree.node D2M8K2.t8386 (nat_lit 18165957) (nat_lit 1515353570) (nat_lit 0) D2M8K2.t8387 from rfl, allE_node, rows8386, irow8382, rows8387]
  all_goals rfl

theorem atot8382 : totK PD2M8K2 D2M8K2.u8382 = [0, 306133018064, 903336387824, 546934964357, 45620042978, 0, 0, 0] := by
  rw [show D2M8K2.u8382 = KTree.node D2M8K2.t8386 (nat_lit 18165957) (nat_lit 1515353570) (nat_lit 0) D2M8K2.t8387 from rfl, totK_node, tot8386, tot8387]
  decide +kernel

theorem arows8384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8384 = true := by
  rw [show D2M8K2.u8384 = KTree.node D2M8K2.t8388 (nat_lit 18167724) (nat_lit 3189829869) (nat_lit 0) D2M8K2.t8389 from rfl, allE_node, rows8388, irow8384, rows8389]
  all_goals rfl

theorem atot8384 : totK PD2M8K2 D2M8K2.u8384 = [0, 139053454770, 714440988497, 811073704649, 137290071553, 1369150432, 0, 0] := by
  rw [show D2M8K2.u8384 = KTree.node D2M8K2.t8388 (nat_lit 18167724) (nat_lit 3189829869) (nat_lit 0) D2M8K2.t8389 from rfl, totK_node, tot8388, tot8389]
  decide +kernel

theorem arows8385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8385 = true := by
  rw [show D2M8K2.u8385 = KTree.node D2M8K2.t8390 (nat_lit 18173089) (nat_lit 1553212496) (nat_lit 0) D2M8K2.t8391 from rfl, allE_node, rows8390, irow8385, rows8391]
  all_goals rfl

theorem atot8385 : totK PD2M8K2 D2M8K2.u8385 = [0, 258795542051, 788552304948, 617839863829, 92943426467, 1164319620, 0, 0] := by
  rw [show D2M8K2.u8385 = KTree.node D2M8K2.t8390 (nat_lit 18173089) (nat_lit 1553212496) (nat_lit 0) D2M8K2.t8391 from rfl, totK_node, tot8390, tot8391]
  decide +kernel

theorem arows8388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8388 = true := by
  rw [show D2M8K2.u8388 = KTree.node D2M8K2.t8392 (nat_lit 18174824) (nat_lit 2433255299) (nat_lit 0) D2M8K2.t8393 from rfl, allE_node, rows8392, irow8388, rows8393]
  all_goals rfl

theorem atot8388 : totK PD2M8K2 D2M8K2.u8388 = [0, 156163025802, 650903724034, 747236419001, 194988479306, 11727338389, 0, 0] := by
  rw [show D2M8K2.u8388 = KTree.node D2M8K2.t8392 (nat_lit 18174824) (nat_lit 2433255299) (nat_lit 0) D2M8K2.t8393 from rfl, totK_node, tot8392, tot8393]
  decide +kernel

theorem arows8389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8389 = true := by
  rw [show D2M8K2.u8389 = KTree.node D2M8K2.t8394 (nat_lit 18176500) (nat_lit 3472059260) (nat_lit 0) D2M8K2.t8395 from rfl, allE_node, rows8394, irow8389, rows8395]
  all_goals rfl

theorem atot8389 : totK PD2M8K2 D2M8K2.u8389 = [0, 262444607528, 795041282710, 633021598027, 95109575903, 1198073392, 0, 0] := by
  rw [show D2M8K2.u8389 = KTree.node D2M8K2.t8394 (nat_lit 18176500) (nat_lit 3472059260) (nat_lit 0) D2M8K2.t8395 from rfl, totK_node, tot8394, tot8395]
  decide +kernel

theorem arows8391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8391 = true := by
  rw [show D2M8K2.u8391 = KTree.node D2M8K2.t8396 (nat_lit 18178202) (nat_lit 3451166169) (nat_lit 0) D2M8K2.t8397 from rfl, allE_node, rows8396, irow8391, rows8397]
  all_goals rfl

theorem atot8391 : totK PD2M8K2 D2M8K2.u8391 = [0, 153157419074, 650413198282, 750576572470, 199208759024, 11894306413, 0, 0] := by
  rw [show D2M8K2.u8391 = KTree.node D2M8K2.t8396 (nat_lit 18178202) (nat_lit 3451166169) (nat_lit 0) D2M8K2.t8397 from rfl, totK_node, tot8396, tot8397]
  decide +kernel

theorem arows8392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8392 = true := by
  rw [show D2M8K2.u8392 = KTree.node D2M8K2.t8398 (nat_lit 18179602) (nat_lit 2636941566) (nat_lit 0) D2M8K2.t8399 from rfl, allE_node, rows8398, irow8392, rows8399]
  all_goals rfl

theorem atot8392 : totK PD2M8K2 D2M8K2.u8392 = [0, 258857866957, 796492114202, 614252804216, 83721121828, 1096505104, 0, 0] := by
  rw [show D2M8K2.u8392 = KTree.node D2M8K2.t8398 (nat_lit 18179602) (nat_lit 2636941566) (nat_lit 0) D2M8K2.t8399 from rfl, totK_node, tot8398, tot8399]
  decide +kernel

end QECKChecks.D2M8K2
