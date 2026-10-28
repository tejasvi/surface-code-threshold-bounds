import QEC.Count.ChunksK3
import QEC.KChecks.A10K2.A5

namespace QECKChecks.A10K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows7196 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7196 = true := by
  rw [show A10K2.u7196 = KTree.node A10K2.t7200 (nat_lit 118783443) (nat_lit 8531556741) (nat_lit 0) A10K2.t7201 from rfl, allE_node, rows7200, irow7196, rows7201]
  all_goals rfl

theorem atot7196 : totK PA10K2 A10K2.u7196 = [0, 0, 578505617916, 2652909927322, 4074554845602, 2224800501152, 326728082688, 6853348008, 0, 0] := by
  rw [show A10K2.u7196 = KTree.node A10K2.t7200 (nat_lit 118783443) (nat_lit 8531556741) (nat_lit 0) A10K2.t7201 from rfl, totK_node, tot7200, tot7201]
  decide +kernel

theorem arows7197 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7197 = true := by
  rw [show A10K2.u7197 = KTree.node A10K2.t7202 (nat_lit 118887026) (nat_lit 1367952827) (nat_lit 0) A10K2.t7203 from rfl, allE_node, rows7202, irow7197, rows7203]
  all_goals rfl

theorem atot7197 : totK PA10K2 A10K2.u7197 = [0, 0, 381768199899, 2058353327490, 3999718919589, 2539486900788, 467316409872, 30074883546, 0, 0] := by
  rw [show A10K2.u7197 = KTree.node A10K2.t7202 (nat_lit 118887026) (nat_lit 1367952827) (nat_lit 0) A10K2.t7203 from rfl, totK_node, tot7202, tot7203]
  decide +kernel

theorem arows7199 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7199 = true := by
  rw [show A10K2.u7199 = KTree.node A10K2.t7204 (nat_lit 118895835) (nat_lit 9773256128) (nat_lit 0) A10K2.t7205 from rfl, allE_node, rows7204, irow7199, rows7205]
  all_goals rfl

theorem atot7199 : totK PA10K2 A10K2.u7199 = [0, 0, 637684454134, 2880209121371, 3985007843450, 1812076181357, 236471759655, 6034215561, 0, 0] := by
  rw [show A10K2.u7199 = KTree.node A10K2.t7204 (nat_lit 118895835) (nat_lit 9773256128) (nat_lit 0) A10K2.t7205 from rfl, totK_node, tot7204, tot7205]
  decide +kernel

theorem arows7200 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7200 = true := by
  rw [show A10K2.u7200 = KTree.node A10K2.t7206 (nat_lit 118900956) (nat_lit 11285371633) (nat_lit 0) A10K2.t7207 from rfl, allE_node, rows7206, irow7200, rows7207]
  all_goals rfl

theorem atot7200 : totK PA10K2 A10K2.u7200 = [0, 0, 546985495730, 2887042430537, 4228446690326, 1572796068479, 118243869024, 0, 0, 0] := by
  rw [show A10K2.u7200 = KTree.node A10K2.t7206 (nat_lit 118900956) (nat_lit 11285371633) (nat_lit 0) A10K2.t7207 from rfl, totK_node, tot7206, tot7207]
  decide +kernel

theorem arows7203 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7203 = true := by
  rw [show A10K2.u7203 = KTree.node A10K2.t7208 (nat_lit 118915877) (nat_lit 7302858717) (nat_lit 0) A10K2.t7209 from rfl, allE_node, rows7208, irow7203, rows7209]
  all_goals rfl

theorem atot7203 : totK PA10K2 A10K2.u7203 = [0, 0, 0, 1174038143973, 3973338453972, 3429129524268, 725274843175, 37547833973, 0, 0] := by
  rw [show A10K2.u7203 = KTree.node A10K2.t7208 (nat_lit 118915877) (nat_lit 7302858717) (nat_lit 0) A10K2.t7209 from rfl, totK_node, tot7208, tot7209]
  decide +kernel

theorem arows7204 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7204 = true := by
  rw [show A10K2.u7204 = KTree.node A10K2.t7210 (nat_lit 118932045) (nat_lit 5371552911) (nat_lit 0) A10K2.t7211 from rfl, allE_node, rows7210, irow7204, rows7211]
  all_goals rfl

theorem atot7204 : totK PA10K2 A10K2.u7204 = [0, 0, 0, 1153346602427, 3930874002331, 3452266042691, 731657274407, 36913694812, 0, 0] := by
  rw [show A10K2.u7204 = KTree.node A10K2.t7210 (nat_lit 118932045) (nat_lit 5371552911) (nat_lit 0) A10K2.t7211 from rfl, totK_node, tot7210, tot7211]
  decide +kernel

theorem arows7206 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7206 = true := by
  rw [show A10K2.u7206 = KTree.node A10K2.t7212 (nat_lit 118938391) (nat_lit 2445474306) (nat_lit 8) A10K2.t7213 from rfl, allE_node, rows7212, irow7206, rows7213]
  all_goals rfl

theorem atot7206 : totK PA10K2 A10K2.u7206 = [0, 540022072669, 1785216125395, 1640850763636, 1360690318501, 2396617572374, 1335643561355, 195382007035, 6354482628, 0] := by
  rw [show A10K2.u7206 = KTree.node A10K2.t7212 (nat_lit 118938391) (nat_lit 2445474306) (nat_lit 8) A10K2.t7213 from rfl, totK_node, tot7212, tot7213]
  decide +kernel

theorem arows7207 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7207 = true := by
  rw [show A10K2.u7207 = KTree.node A10K2.t7214 (nat_lit 119017810) (nat_lit 3419728550) (nat_lit 0) A10K2.t7215 from rfl, allE_node, rows7214, irow7207, rows7215]
  all_goals rfl

theorem atot7207 : totK PA10K2 A10K2.u7207 = [0, 295901161011, 1957886044047, 3981717994230, 2737855390158, 567144434603, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u7207 = KTree.node A10K2.t7214 (nat_lit 119017810) (nat_lit 3419728550) (nat_lit 0) A10K2.t7215 from rfl, totK_node, tot7214, tot7215]
  decide +kernel

theorem arows7211 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7211 = true := by
  rw [show A10K2.u7211 = KTree.node A10K2.t7216 (nat_lit 119032108) (nat_lit 13552313479) (nat_lit 0) A10K2.t7217 from rfl, allE_node, rows7216, irow7211, rows7217]
  all_goals rfl

theorem atot7211 : totK PA10K2 A10K2.u7211 = [0, 536206938430, 2543983574755, 4006083816215, 2048597573257, 268068431435, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u7211 = KTree.node A10K2.t7216 (nat_lit 119032108) (nat_lit 13552313479) (nat_lit 0) A10K2.t7217 from rfl, totK_node, tot7216, tot7217]
  decide +kernel

theorem arows7212 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7212 = true := by
  rw [show A10K2.u7212 = KTree.node A10K2.t7218 (nat_lit 119041064) (nat_lit 12291586482) (nat_lit 0) A10K2.t7219 from rfl, allE_node, rows7218, irow7212, rows7219]
  all_goals rfl

theorem atot7212 : totK PA10K2 A10K2.u7212 = [0, 804845363582, 3301668047036, 4229629063363, 1716308090306, 165306031355, 0, 0, 0, 0] := by
  rw [show A10K2.u7212 = KTree.node A10K2.t7218 (nat_lit 119041064) (nat_lit 12291586482) (nat_lit 0) A10K2.t7219 from rfl, totK_node, tot7218, tot7219]
  decide +kernel

theorem arows7214 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7214 = true := by
  rw [show A10K2.u7214 = KTree.node A10K2.t7220 (nat_lit 119045729) (nat_lit 3982414036) (nat_lit 0) A10K2.t7221 from rfl, allE_node, rows7220, irow7214, rows7221]
  all_goals rfl

theorem atot7214 : totK PA10K2 A10K2.u7214 = [0, 0, 955160948351, 3613877687944, 4128270685431, 1295746742614, 88646843074, 0, 0, 0] := by
  rw [show A10K2.u7214 = KTree.node A10K2.t7220 (nat_lit 119045729) (nat_lit 3982414036) (nat_lit 0) A10K2.t7221 from rfl, totK_node, tot7220, tot7221]
  decide +kernel

theorem arows7215 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7215 = true := by
  rw [show A10K2.u7215 = KTree.node A10K2.t7222 (nat_lit 119050305) (nat_lit 10405391659) (nat_lit 0) A10K2.t7223 from rfl, allE_node, rows7222, irow7215, rows7223]
  all_goals rfl

theorem atot7215 : totK PA10K2 A10K2.u7215 = [0, 0, 400811964952, 2180550502656, 3754673821121, 2374570963746, 522666646714, 30650496230, 0, 0] := by
  rw [show A10K2.u7215 = KTree.node A10K2.t7222 (nat_lit 119050305) (nat_lit 10405391659) (nat_lit 0) A10K2.t7223 from rfl, totK_node, tot7222, tot7223]
  decide +kernel

theorem arows7218 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7218 = true := by
  rw [show A10K2.u7218 = KTree.node A10K2.t7224 (nat_lit 119064837) (nat_lit 7040787894) (nat_lit 0) A10K2.t7225 from rfl, allE_node, rows7224, irow7218, rows7225]
  all_goals rfl

theorem atot7218 : totK PA10K2 A10K2.u7218 = [0, 0, 518259217515, 2647763393718, 4107376749027, 1884722578903, 206740800434, 0, 0, 0] := by
  rw [show A10K2.u7218 = KTree.node A10K2.t7224 (nat_lit 119064837) (nat_lit 7040787894) (nat_lit 0) A10K2.t7225 from rfl, totK_node, tot7224, tot7225]
  decide +kernel

theorem arows7219 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7219 = true := by
  rw [show A10K2.u7219 = KTree.node A10K2.t7226 (nat_lit 119073850) (nat_lit 11555965563) (nat_lit 0) A10K2.t7227 from rfl, allE_node, rows7226, irow7219, rows7227]
  all_goals rfl

theorem atot7219 : totK PA10K2 A10K2.u7219 = [0, 305030648051, 1696446878539, 3619039262690, 3402710073593, 1064730449303, 115892485707, 5546304973, 0, 0] := by
  rw [show A10K2.u7219 = KTree.node A10K2.t7226 (nat_lit 119073850) (nat_lit 11555965563) (nat_lit 0) A10K2.t7227 from rfl, totK_node, tot7226, tot7227]
  decide +kernel

theorem arows7221 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7221 = true := by
  rw [show A10K2.u7221 = KTree.node A10K2.t7228 (nat_lit 119090902) (nat_lit 15136587392) (nat_lit 0) A10K2.t7229 from rfl, allE_node, rows7228, irow7221, rows7229]
  all_goals rfl

theorem atot7221 : totK PA10K2 A10K2.u7221 = [0, 474796662945, 2454195925280, 4170641865384, 2477622075746, 431558391075, 13576218110, 0, 0, 0] := by
  rw [show A10K2.u7221 = KTree.node A10K2.t7228 (nat_lit 119090902) (nat_lit 15136587392) (nat_lit 0) A10K2.t7229 from rfl, totK_node, tot7228, tot7229]
  decide +kernel

theorem arows7222 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7222 = true := by
  rw [show A10K2.u7222 = KTree.node A10K2.t7230 (nat_lit 119104925) (nat_lit 4910398211) (nat_lit 0) A10K2.t7231 from rfl, allE_node, rows7230, irow7222, rows7231]
  all_goals rfl

theorem atot7222 : totK PA10K2 A10K2.u7222 = [0, 826908269086, 3342159372993, 4269197895100, 1758414969541, 144980448960, 0, 0, 0, 0] := by
  rw [show A10K2.u7222 = KTree.node A10K2.t7230 (nat_lit 119104925) (nat_lit 4910398211) (nat_lit 0) A10K2.t7231 from rfl, totK_node, tot7230, tot7231]
  decide +kernel

theorem arows7228 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7228 = true := by
  rw [show A10K2.u7228 = KTree.node A10K2.t7232 (nat_lit 119110727) (nat_lit 11210411356) (nat_lit 0) A10K2.t7233 from rfl, allE_node, rows7232, irow7228, rows7233]
  all_goals rfl

theorem atot7228 : totK PA10K2 A10K2.u7228 = [0, 0, 1129425610948, 3952649476709, 4001689404957, 1092427968808, 62978488420, 0, 0, 0] := by
  rw [show A10K2.u7228 = KTree.node A10K2.t7232 (nat_lit 119110727) (nat_lit 11210411356) (nat_lit 0) A10K2.t7233 from rfl, totK_node, tot7232, tot7233]
  decide +kernel

theorem arows7229 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7229 = true := by
  rw [show A10K2.u7229 = KTree.node A10K2.t7234 (nat_lit 119123699) (nat_lit 9156035615) (nat_lit 0) A10K2.t7235 from rfl, allE_node, rows7234, irow7229, rows7235]
  all_goals rfl

theorem atot7229 : totK PA10K2 A10K2.u7229 = [0, 0, 473974092908, 2415539989728, 4128468950598, 2430756450722, 418279937773, 13576218110, 0, 0] := by
  rw [show A10K2.u7229 = KTree.node A10K2.t7234 (nat_lit 119123699) (nat_lit 9156035615) (nat_lit 0) A10K2.t7235 from rfl, totK_node, tot7234, tot7235]
  decide +kernel

theorem arows7231 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7231 = true := by
  rw [show A10K2.u7231 = KTree.node A10K2.t7236 (nat_lit 119137949) (nat_lit 5886047895) (nat_lit 0) A10K2.t7237 from rfl, allE_node, rows7236, irow7231, rows7237]
  all_goals rfl

theorem atot7231 : totK PA10K2 A10K2.u7231 = [0, 113839911969, 1057759139770, 3418696532869, 4067271813311, 1518059004776, 121595227027, 0, 0, 0] := by
  rw [show A10K2.u7231 = KTree.node A10K2.t7236 (nat_lit 119137949) (nat_lit 5886047895) (nat_lit 0) A10K2.t7237 from rfl, totK_node, tot7236, tot7237]
  decide +kernel

theorem arows7232 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7232 = true := by
  rw [show A10K2.u7232 = KTree.node A10K2.t7238 (nat_lit 119213234) (nat_lit 14660878353) (nat_lit 0) A10K2.t7239 from rfl, allE_node, rows7238, irow7232, rows7239]
  all_goals rfl

theorem atot7232 : totK PA10K2 A10K2.u7232 = [0, 663984757638, 2916258198052, 4010862498605, 1870221490633, 307264649870, 20029934272, 0, 0, 0] := by
  rw [show A10K2.u7232 = KTree.node A10K2.t7238 (nat_lit 119213234) (nat_lit 14660878353) (nat_lit 0) A10K2.t7239 from rfl, totK_node, tot7238, tot7239]
  decide +kernel

theorem arows7235 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7235 = true := by
  rw [show A10K2.u7235 = KTree.node A10K2.t7240 (nat_lit 119219632) (nat_lit 12017384582) (nat_lit 0) A10K2.t7241 from rfl, allE_node, rows7240, irow7235, rows7241]
  all_goals rfl

theorem atot7235 : totK PA10K2 A10K2.u7235 = [0, 685882265884, 2884700355905, 4065952687804, 2070758156023, 326429369748, 10719219105, 0, 0, 0] := by
  rw [show A10K2.u7235 = KTree.node A10K2.t7240 (nat_lit 119219632) (nat_lit 12017384582) (nat_lit 0) A10K2.t7241 from rfl, totK_node, tot7240, tot7241]
  decide +kernel

theorem arows7236 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7236 = true := by
  rw [show A10K2.u7236 = KTree.node A10K2.t7242 (nat_lit 119225565) (nat_lit 5329251160) (nat_lit 0) A10K2.t7243 from rfl, allE_node, rows7242, irow7236, rows7243]
  all_goals rfl

theorem atot7236 : totK PA10K2 A10K2.u7236 = [0, 552204907645, 2522618480829, 4002592454828, 2520710399299, 470748274188, 18609374344, 0, 0, 0] := by
  rw [show A10K2.u7236 = KTree.node A10K2.t7242 (nat_lit 119225565) (nat_lit 5329251160) (nat_lit 0) A10K2.t7243 from rfl, totK_node, tot7242, tot7243]
  decide +kernel

theorem arows7238 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7238 = true := by
  rw [show A10K2.u7238 = KTree.node A10K2.t7244 (nat_lit 119238664) (nat_lit 14535656381) (nat_lit 0) A10K2.t7245 from rfl, allE_node, rows7244, irow7238, rows7245]
  all_goals rfl

theorem atot7238 : totK PA10K2 A10K2.u7238 = [0, 330854518425, 2078483292764, 4187873386409, 2907899485686, 530228959723, 13816090359, 0, 0, 0] := by
  rw [show A10K2.u7238 = KTree.node A10K2.t7244 (nat_lit 119238664) (nat_lit 14535656381) (nat_lit 0) A10K2.t7245 from rfl, totK_node, tot7244, tot7245]
  decide +kernel

theorem arows7239 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7239 = true := by
  rw [show A10K2.u7239 = KTree.node A10K2.t7246 (nat_lit 119243219) (nat_lit 6839662721) (nat_lit 0) A10K2.t7247 from rfl, allE_node, rows7246, irow7239, rows7247]
  all_goals rfl

theorem atot7239 : totK PA10K2 A10K2.u7239 = [0, 0, 1106137120960, 3792699755550, 3804880452763, 1110711480666, 80190721993, 0, 0, 0] := by
  rw [show A10K2.u7239 = KTree.node A10K2.t7246 (nat_lit 119243219) (nat_lit 6839662721) (nat_lit 0) A10K2.t7247 from rfl, totK_node, tot7246, tot7247]
  decide +kernel

theorem arows7243 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7243 = true := by
  rw [show A10K2.u7243 = KTree.node A10K2.t7248 (nat_lit 119249223) (nat_lit 2670684934) (nat_lit 0) A10K2.t7249 from rfl, allE_node, rows7248, irow7243, rows7249]
  all_goals rfl

theorem atot7243 : totK PA10K2 A10K2.u7243 = [0, 0, 378133059829, 2292373955469, 4318716607860, 2537542860769, 354820184623, 6904928264, 0, 0] := by
  rw [show A10K2.u7243 = KTree.node A10K2.t7248 (nat_lit 119249223) (nat_lit 2670684934) (nat_lit 0) A10K2.t7249 from rfl, totK_node, tot7248, tot7249]
  decide +kernel

theorem arows7244 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7244 = true := by
  rw [show A10K2.u7244 = KTree.node A10K2.t7250 (nat_lit 119256538) (nat_lit 14639681862) (nat_lit 0) A10K2.t7251 from rfl, allE_node, rows7250, irow7244, rows7251]
  all_goals rfl

theorem atot7244 : totK PA10K2 A10K2.u7244 = [0, 0, 588771301104, 2797734356815, 4217569144337, 2243181904724, 309584972983, 7047025452, 0, 0] := by
  rw [show A10K2.u7244 = KTree.node A10K2.t7250 (nat_lit 119256538) (nat_lit 14639681862) (nat_lit 0) A10K2.t7251 from rfl, totK_node, tot7250, tot7251]
  decide +kernel

theorem arows7246 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7246 = true := by
  rw [show A10K2.u7246 = KTree.node A10K2.t7252 (nat_lit 119270854) (nat_lit 15871218281) (nat_lit 0) A10K2.t7253 from rfl, allE_node, rows7252, irow7246, rows7253]
  all_goals rfl

theorem atot7246 : totK PA10K2 A10K2.u7246 = [0, 0, 599785301940, 2760368310961, 4120891471894, 2144709812910, 280262440278, 6066958478, 0, 0] := by
  rw [show A10K2.u7246 = KTree.node A10K2.t7252 (nat_lit 119270854) (nat_lit 15871218281) (nat_lit 0) A10K2.t7253 from rfl, totK_node, tot7252, tot7253]
  decide +kernel

theorem arows7247 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7247 = true := by
  rw [show A10K2.u7247 = KTree.node A10K2.t7254 (nat_lit 119275454) (nat_lit 16396326754) (nat_lit 0) A10K2.t7255 from rfl, allE_node, rows7254, irow7247, rows7255]
  all_goals rfl

theorem atot7247 : totK PA10K2 A10K2.u7247 = [0, 0, 540022072669, 2270596572691, 3533318715830, 2598342462916, 738207838133, 55043167628, 0, 0] := by
  rw [show A10K2.u7247 = KTree.node A10K2.t7254 (nat_lit 119275454) (nat_lit 16396326754) (nat_lit 0) A10K2.t7255 from rfl, totK_node, tot7254, tot7255]
  decide +kernel

theorem arows7250 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7250 = true := by
  rw [show A10K2.u7250 = KTree.node A10K2.t7256 (nat_lit 119279956) (nat_lit 10606797946) (nat_lit 0) A10K2.t7257 from rfl, allE_node, rows7256, irow7250, rows7257]
  all_goals rfl

theorem atot7250 : totK PA10K2 A10K2.u7250 = [0, 0, 295901161011, 1984152158568, 3973742938116, 2700373288825, 562785275396, 30780440178, 0, 0] := by
  rw [show A10K2.u7250 = KTree.node A10K2.t7256 (nat_lit 119279956) (nat_lit 10606797946) (nat_lit 0) A10K2.t7257 from rfl, totK_node, tot7256, tot7257]
  decide +kernel

theorem arows7251 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7251 = true := by
  rw [show A10K2.u7251 = KTree.node A10K2.t7258 (nat_lit 119294276) (nat_lit 13109807505) (nat_lit 0) A10K2.t7259 from rfl, allE_node, rows7258, irow7251, rows7259]
  all_goals rfl

theorem atot7251 : totK PA10K2 A10K2.u7251 = [0, 0, 562609111720, 2569361552884, 3974695382884, 1977821018684, 263991472526, 5705019915, 0, 0] := by
  rw [show A10K2.u7251 = KTree.node A10K2.t7258 (nat_lit 119294276) (nat_lit 13109807505) (nat_lit 0) A10K2.t7259 from rfl, totK_node, tot7258, tot7259]
  decide +kernel

theorem arows7253 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7253 = true := by
  rw [show A10K2.u7253 = KTree.node A10K2.t7260 (nat_lit 119303223) (nat_lit 14949959527) (nat_lit 0) A10K2.t7261 from rfl, allE_node, rows7260, irow7253, rows7261]
  all_goals rfl

theorem atot7253 : totK PA10K2 A10K2.u7253 = [0, 0, 778443190292, 3254818160480, 4241438453686, 1742121631138, 168447117088, 0, 0, 0] := by
  rw [show A10K2.u7253 = KTree.node A10K2.t7260 (nat_lit 119303223) (nat_lit 14949959527) (nat_lit 0) A10K2.t7261 from rfl, totK_node, tot7260, tot7261]
  decide +kernel

theorem arows7254 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7254 = true := by
  rw [show A10K2.u7254 = KTree.node A10K2.t7262 (nat_lit 119307922) (nat_lit 15114700329) (nat_lit 0) A10K2.t7263 from rfl, allE_node, rows7262, irow7254, rows7263]
  all_goals rfl

theorem atot7254 : totK PA10K2 A10K2.u7254 = [0, 0, 0, 969738090938, 3616845572545, 4087910331370, 1274183809708, 87926673087, 0, 0] := by
  rw [show A10K2.u7254 = KTree.node A10K2.t7262 (nat_lit 119307922) (nat_lit 15114700329) (nat_lit 0) A10K2.t7263 from rfl, totK_node, tot7262, tot7263]
  decide +kernel

theorem arows7259 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7259 = true := by
  rw [show A10K2.u7259 = KTree.node A10K2.t7264 (nat_lit 119312480) (nat_lit 13870624922) (nat_lit 0) A10K2.t7265 from rfl, allE_node, rows7264, irow7259, rows7265]
  all_goals rfl

theorem atot7259 : totK PA10K2 A10K2.u7259 = [0, 0, 0, 463392814351, 2502116288911, 4127679535211, 2131102739350, 302728369852, 7007974415, 0] := by
  rw [show A10K2.u7259 = KTree.node A10K2.t7264 (nat_lit 119312480) (nat_lit 13870624922) (nat_lit 0) A10K2.t7265 from rfl, totK_node, tot7264, tot7265]
  decide +kernel

theorem arows7260 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7260 = true := by
  rw [show A10K2.u7260 = KTree.node A10K2.t7266 (nat_lit 119332934) (nat_lit 14943008976) (nat_lit 0) A10K2.t7267 from rfl, allE_node, rows7266, irow7260, rows7267]
  all_goals rfl

theorem atot7260 : totK PA10K2 A10K2.u7260 = [0, 0, 0, 1123645360838, 3972223305662, 3802506508419, 820039533792, 29895864285, 0, 0] := by
  rw [show A10K2.u7260 = KTree.node A10K2.t7266 (nat_lit 119332934) (nat_lit 14943008976) (nat_lit 0) A10K2.t7267 from rfl, totK_node, tot7266, tot7267]
  decide +kernel

theorem arows7262 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7262 = true := by
  rw [show A10K2.u7262 = KTree.node A10K2.t7268 (nat_lit 119351058) (nat_lit 15163172844) (nat_lit 0) A10K2.t7269 from rfl, allE_node, rows7268, irow7262, rows7269]
  all_goals rfl

theorem atot7262 : totK PA10K2 A10K2.u7262 = [0, 0, 779329081182, 2980725127582, 3732766950753, 2019751785865, 573698923216, 50425690648, 0, 0] := by
  rw [show A10K2.u7262 = KTree.node A10K2.t7268 (nat_lit 119351058) (nat_lit 15163172844) (nat_lit 0) A10K2.t7269 from rfl, totK_node, tot7268, tot7269]
  decide +kernel

theorem arows7263 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7263 = true := by
  rw [show A10K2.u7263 = KTree.node A10K2.t7270 (nat_lit 119356489) (nat_lit 6153328429) (nat_lit 0) A10K2.t7271 from rfl, allE_node, rows7270, irow7263, rows7271]
  all_goals rfl

theorem atot7263 : totK PA10K2 A10K2.u7263 = [0, 0, 504782908657, 2393291503861, 4061423375589, 2717622262362, 485884400820, 13576218110, 0, 0] := by
  rw [show A10K2.u7263 = KTree.node A10K2.t7270 (nat_lit 119356489) (nat_lit 6153328429) (nat_lit 0) A10K2.t7271 from rfl, totK_node, tot7270, tot7271]
  decide +kernel

theorem arows7266 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7266 = true := by
  rw [show A10K2.u7266 = KTree.node A10K2.t7272 (nat_lit 119369806) (nat_lit 10904956324) (nat_lit 0) A10K2.t7273 from rfl, allE_node, rows7272, irow7266, rows7273]
  all_goals rfl

theorem atot7266 : totK PA10K2 A10K2.u7266 = [0, 0, 320625971501, 2125016061316, 4318733946671, 2974086448765, 518960103865, 13242594235, 0, 0] := by
  rw [show A10K2.u7266 = KTree.node A10K2.t7272 (nat_lit 119369806) (nat_lit 10904956324) (nat_lit 0) A10K2.t7273 from rfl, totK_node, tot7272, tot7273]
  decide +kernel

theorem arows7267 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7267 = true := by
  rw [show A10K2.u7267 = KTree.node A10K2.t7274 (nat_lit 119383876) (nat_lit 5423232771) (nat_lit 8) A10K2.t7275 from rfl, allE_node, rows7274, irow7267, rows7275]
  all_goals rfl

theorem atot7267 : totK PA10K2 A10K2.u7267 = [0, 0, 0, 898558405378, 3538841431363, 4170947555975, 1398638409416, 97270495374, 0, 0] := by
  rw [show A10K2.u7267 = KTree.node A10K2.t7274 (nat_lit 119383876) (nat_lit 5423232771) (nat_lit 8) A10K2.t7275 from rfl, totK_node, tot7274, tot7275]
  decide +kernel

theorem arows7269 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7269 = true := by
  rw [show A10K2.u7269 = KTree.node A10K2.t7276 (nat_lit 119398811) (nat_lit 8407860719) (nat_lit 0) A10K2.t7277 from rfl, allE_node, rows7276, irow7269, rows7277]
  all_goals rfl

theorem atot7269 : totK PA10K2 A10K2.u7269 = [0, 0, 0, 703267162882, 3046718275323, 4223645647637, 1862275574957, 231757601539, 7151180950, 0] := by
  rw [show A10K2.u7269 = KTree.node A10K2.t7276 (nat_lit 119398811) (nat_lit 8407860719) (nat_lit 0) A10K2.t7277 from rfl, totK_node, tot7276, tot7277]
  decide +kernel

theorem arows7270 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7270 = true := by
  rw [show A10K2.u7270 = KTree.node A10K2.t7278 (nat_lit 119472965) (nat_lit 5957208220) (nat_lit 0) A10K2.t7279 from rfl, allE_node, rows7278, irow7270, rows7279]
  all_goals rfl

theorem atot7270 : totK PA10K2 A10K2.u7270 = [0, 0, 777824669607, 2963837118783, 3645641232786, 1954667105708, 570007629123, 50432252117, 0, 0] := by
  rw [show A10K2.u7270 = KTree.node A10K2.t7278 (nat_lit 119472965) (nat_lit 5957208220) (nat_lit 0) A10K2.t7279 from rfl, totK_node, tot7278, tot7279]
  decide +kernel

theorem arows7274 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7274 = true := by
  rw [show A10K2.u7274 = KTree.node A10K2.t7280 (nat_lit 119479369) (nat_lit 9357096516) (nat_lit 0) A10K2.t7281 from rfl, allE_node, rows7280, irow7274, rows7281]
  all_goals rfl

theorem atot7274 : totK PA10K2 A10K2.u7274 = [0, 0, 459159501540, 2278935084535, 4056550164005, 2613189284651, 465945891667, 11991740650, 0, 0] := by
  rw [show A10K2.u7274 = KTree.node A10K2.t7280 (nat_lit 119479369) (nat_lit 9357096516) (nat_lit 0) A10K2.t7281 from rfl, totK_node, tot7280, tot7281]
  decide +kernel

theorem arows7275 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7275 = true := by
  rw [show A10K2.u7275 = KTree.node A10K2.t7282 (nat_lit 119486162) (nat_lit 15271571326) (nat_lit 0) A10K2.t7283 from rfl, allE_node, rows7282, irow7275, rows7283]
  all_goals rfl

theorem atot7275 : totK PA10K2 A10K2.u7275 = [0, 0, 507940243355, 2529317414272, 4144312131290, 2556606759351, 413235424354, 12219140272, 0, 0] := by
  rw [show A10K2.u7275 = KTree.node A10K2.t7282 (nat_lit 119486162) (nat_lit 15271571326) (nat_lit 0) A10K2.t7283 from rfl, totK_node, tot7282, tot7283]
  decide +kernel

theorem arows7277 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7277 = true := by
  rw [show A10K2.u7277 = KTree.node A10K2.t7284 (nat_lit 119500188) (nat_lit 7397321093) (nat_lit 0) A10K2.t7285 from rfl, allE_node, rows7284, irow7277, rows7285]
  all_goals rfl

theorem atot7277 : totK PA10K2 A10K2.u7277 = [0, 0, 600351679897, 2743565327122, 4148730999683, 2196976204051, 303273351362, 6772895877, 0, 0] := by
  rw [show A10K2.u7277 = KTree.node A10K2.t7284 (nat_lit 119500188) (nat_lit 7397321093) (nat_lit 0) A10K2.t7285 from rfl, totK_node, tot7284, tot7285]
  decide +kernel

theorem arows7278 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7278 = true := by
  rw [show A10K2.u7278 = KTree.node A10K2.t7286 (nat_lit 119504625) (nat_lit 5615272882) (nat_lit 0) A10K2.t7287 from rfl, allE_node, rows7286, irow7278, rows7287]
  all_goals rfl

theorem atot7278 : totK PA10K2 A10K2.u7278 = [0, 0, 0, 1016954126408, 3725305866898, 3973681693309, 1134080620773, 68058142506, 0, 0] := by
  rw [show A10K2.u7278 = KTree.node A10K2.t7286 (nat_lit 119504625) (nat_lit 5615272882) (nat_lit 0) A10K2.t7287 from rfl, totK_node, tot7286, tot7287]
  decide +kernel

theorem arows7281 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7281 = true := by
  rw [show A10K2.u7281 = KTree.node A10K2.t7288 (nat_lit 119509537) (nat_lit 10123403547) (nat_lit 0) A10K2.t7289 from rfl, allE_node, rows7288, irow7281, rows7289]
  all_goals rfl

theorem atot7281 : totK PA10K2 A10K2.u7281 = [0, 0, 0, 563564815499, 2751768004624, 4198660611672, 2116606459427, 272646473745, 6318667960, 0] := by
  rw [show A10K2.u7281 = KTree.node A10K2.t7288 (nat_lit 119509537) (nat_lit 10123403547) (nat_lit 0) A10K2.t7289 from rfl, totK_node, tot7288, tot7289]
  decide +kernel

theorem arows7282 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7282 = true := by
  rw [show A10K2.u7282 = KTree.node A10K2.t7290 (nat_lit 119518365) (nat_lit 5913814394) (nat_lit 0) A10K2.t7291 from rfl, allE_node, rows7290, irow7282, rows7291]
  all_goals rfl

theorem atot7282 : totK PA10K2 A10K2.u7282 = [0, 0, 0, 565019724202, 2676539028485, 4240980651663, 2246477675388, 289377391356, 6439430839, 0] := by
  rw [show A10K2.u7282 = KTree.node A10K2.t7290 (nat_lit 119518365) (nat_lit 5913814394) (nat_lit 0) A10K2.t7291 from rfl, totK_node, tot7290, tot7291]
  decide +kernel

theorem arows7284 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7284 = true := by
  rw [show A10K2.u7284 = KTree.node A10K2.t7292 (nat_lit 119532641) (nat_lit 9065984947) (nat_lit 0) A10K2.t7293 from rfl, allE_node, rows7292, irow7284, rows7293]
  all_goals rfl

theorem atot7284 : totK PA10K2 A10K2.u7284 = [0, 0, 0, 711760828710, 3122024083599, 4155414774386, 1735650444106, 163009327103, 0, 0] := by
  rw [show A10K2.u7284 = KTree.node A10K2.t7292 (nat_lit 119532641) (nat_lit 9065984947) (nat_lit 0) A10K2.t7293 from rfl, totK_node, tot7292, tot7293]
  decide +kernel

theorem arows7285 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7285 = true := by
  rw [show A10K2.u7285 = KTree.node A10K2.t7294 (nat_lit 119537210) (nat_lit 11323210669) (nat_lit 0) A10K2.t7295 from rfl, allE_node, rows7294, irow7285, rows7295]
  all_goals rfl

theorem atot7285 : totK PA10K2 A10K2.u7285 = [0, 0, 428122261071, 1391660659468, 1937038517661, 2657580322490, 2566537848162, 810410189000, 61018386929, 0] := by
  rw [show A10K2.u7285 = KTree.node A10K2.t7294 (nat_lit 119537210) (nat_lit 11323210669) (nat_lit 0) A10K2.t7295 from rfl, totK_node, tot7294, tot7295]
  decide +kernel

theorem arows7292 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7292 = true := by
  rw [show A10K2.u7292 = KTree.node A10K2.t7296 (nat_lit 119541703) (nat_lit 14288936747) (nat_lit 0) A10K2.t7297 from rfl, allE_node, rows7296, irow7292, rows7297]
  all_goals rfl

theorem atot7292 : totK PA10K2 A10K2.u7292 = [0, 0, 441777860914, 2362774655444, 4001759465911, 2304248124115, 435388037267, 25371180993, 0, 0] := by
  rw [show A10K2.u7292 = KTree.node A10K2.t7296 (nat_lit 119541703) (nat_lit 14288936747) (nat_lit 0) A10K2.t7297 from rfl, totK_node, tot7296, tot7297]
  decide +kernel

theorem arows7293 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7293 = true := by
  rw [show A10K2.u7293 = KTree.node A10K2.t7298 (nat_lit 119554912) (nat_lit 12608668612) (nat_lit 0) A10K2.t7299 from rfl, allE_node, rows7298, irow7293, rows7299]
  all_goals rfl

theorem atot7293 : totK PA10K2 A10K2.u7293 = [0, 0, 682068350716, 2896785843650, 3813369965412, 1697474158127, 227426905256, 5460492893, 0, 0] := by
  rw [show A10K2.u7293 = KTree.node A10K2.t7298 (nat_lit 119554912) (nat_lit 12608668612) (nat_lit 0) A10K2.t7299 from rfl, totK_node, tot7298, tot7299]
  decide +kernel

theorem arows7295 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7295 = true := by
  rw [show A10K2.u7295 = KTree.node A10K2.t7300 (nat_lit 119562530) (nat_lit 7493371317) (nat_lit 0) A10K2.t7301 from rfl, allE_node, rows7300, irow7295, rows7301]
  all_goals rfl

theorem atot7295 : totK PA10K2 A10K2.u7295 = [0, 0, 725221058513, 2879554051272, 3938244414827, 1806870201288, 220346859050, 6354482628, 0, 0] := by
  rw [show A10K2.u7295 = KTree.node A10K2.t7300 (nat_lit 119562530) (nat_lit 7493371317) (nat_lit 0) A10K2.t7301 from rfl, totK_node, tot7300, tot7301]
  decide +kernel

theorem arows7296 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7296 = true := by
  rw [show A10K2.u7296 = KTree.node A10K2.t7302 (nat_lit 119567536) (nat_lit 10307510823) (nat_lit 0) A10K2.t7303 from rfl, allE_node, rows7302, irow7296, rows7303]
  all_goals rfl

theorem atot7296 : totK PA10K2 A10K2.u7296 = [0, 0, 45768258037, 1402649420960, 4005089166553, 3666264572004, 947147276213, 47398443899, 0, 0] := by
  rw [show A10K2.u7296 = KTree.node A10K2.t7302 (nat_lit 119567536) (nat_lit 10307510823) (nat_lit 0) A10K2.t7303 from rfl, totK_node, tot7302, tot7303]
  decide +kernel

theorem arows7299 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7299 = true := by
  rw [show A10K2.u7299 = KTree.node A10K2.t7304 (nat_lit 119573253) (nat_lit 6998560998) (nat_lit 0) A10K2.t7305 from rfl, allE_node, rows7304, irow7299, rows7305]
  all_goals rfl

theorem atot7299 : totK PA10K2 A10K2.u7299 = [0, 0, 0, 801446202028, 3375482184205, 4073416218753, 1329692629262, 93048898234, 0, 0] := by
  rw [show A10K2.u7299 = KTree.node A10K2.t7304 (nat_lit 119573253) (nat_lit 6998560998) (nat_lit 0) A10K2.t7305 from rfl, totK_node, tot7304, tot7305]
  decide +kernel

theorem arows7300 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7300 = true := by
  rw [show A10K2.u7300 = KTree.node A10K2.t7306 (nat_lit 119578056) (nat_lit 13686576100) (nat_lit 0) A10K2.t7307 from rfl, allE_node, rows7306, irow7300, rows7307]
  all_goals rfl

theorem atot7300 : totK PA10K2 A10K2.u7300 = [0, 0, 0, 510545450608, 2293638628144, 3618777304003, 2268318078697, 519206634531, 30650496230, 0] := by
  rw [show A10K2.u7300 = KTree.node A10K2.t7306 (nat_lit 119578056) (nat_lit 13686576100) (nat_lit 0) A10K2.t7307 from rfl, totK_node, tot7306, tot7307]
  decide +kernel

theorem arows7302 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7302 = true := by
  rw [show A10K2.u7302 = KTree.node A10K2.t7308 (nat_lit 119593125) (nat_lit 7333572875) (nat_lit 0) A10K2.t7309 from rfl, allE_node, rows7308, irow7302, rows7309]
  all_goals rfl

theorem atot7302 : totK PA10K2 A10K2.u7302 = [0, 0, 0, 590179586333, 2732828448695, 3949611957866, 1701236761407, 219178372242, 5546304973, 0] := by
  rw [show A10K2.u7302 = KTree.node A10K2.t7308 (nat_lit 119593125) (nat_lit 7333572875) (nat_lit 0) A10K2.t7309 from rfl, totK_node, tot7308, tot7309]
  decide +kernel

theorem arows7303 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7303 = true := by
  rw [show A10K2.u7303 = KTree.node A10K2.t7310 (nat_lit 119668851) (nat_lit 3278906174) (nat_lit 0) A10K2.t7311 from rfl, allE_node, rows7310, irow7303, rows7311]
  all_goals rfl

theorem atot7303 : totK PA10K2 A10K2.u7303 = [0, 0, 576996404534, 2454873603102, 3669484606330, 2376227080961, 669104657213, 41737205306, 0, 0] := by
  rw [show A10K2.u7303 = KTree.node A10K2.t7310 (nat_lit 119668851) (nat_lit 3278906174) (nat_lit 0) A10K2.t7311 from rfl, totK_node, tot7310, tot7311]
  decide +kernel

theorem arows7307 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7307 = true := by
  rw [show A10K2.u7307 = KTree.node A10K2.t7312 (nat_lit 119673669) (nat_lit 6297142131) (nat_lit 0) A10K2.t7313 from rfl, allE_node, rows7312, irow7307, rows7313]
  all_goals rfl

theorem atot7307 : totK PA10K2 A10K2.u7307 = [0, 0, 398112584554, 2001577555582, 3907737549840, 2843819584518, 585850044780, 30831673886, 0, 0] := by
  rw [show A10K2.u7307 = KTree.node A10K2.t7312 (nat_lit 119673669) (nat_lit 6297142131) (nat_lit 0) A10K2.t7313 from rfl, totK_node, tot7312, tot7313]
  decide +kernel

theorem arows7308 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7308 = true := by
  rw [show A10K2.u7308 = KTree.node A10K2.t7314 (nat_lit 119685513) (nat_lit 9610661542) (nat_lit 0) A10K2.t7315 from rfl, allE_node, rows7314, irow7308, rows7315]
  all_goals rfl

theorem atot7308 : totK PA10K2 A10K2.u7308 = [0, 0, 814676512115, 3169845651250, 3732852621280, 1489048967888, 159562116243, 6034215561, 0, 0] := by
  rw [show A10K2.u7308 = KTree.node A10K2.t7314 (nat_lit 119685513) (nat_lit 9610661542) (nat_lit 0) A10K2.t7315 from rfl, totK_node, tot7314, tot7315]
  decide +kernel

theorem arows7310 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7310 = true := by
  rw [show A10K2.u7310 = KTree.node A10K2.t7316 (nat_lit 119691591) (nat_lit 4495269509) (nat_lit 0) A10K2.t7317 from rfl, allE_node, rows7316, irow7310, rows7317]
  all_goals rfl

theorem atot7310 : totK PA10K2 A10K2.u7310 = [0, 0, 0, 1480776806287, 4226314252966, 3080373940810, 584138443952, 31987755669, 0, 0] := by
  rw [show A10K2.u7310 = KTree.node A10K2.t7316 (nat_lit 119691591) (nat_lit 4495269509) (nat_lit 0) A10K2.t7317 from rfl, totK_node, tot7316, tot7317]
  decide +kernel

theorem arows7311 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7311 = true := by
  rw [show A10K2.u7311 = KTree.node A10K2.t7318 (nat_lit 119712035) (nat_lit 10160992118) (nat_lit 0) A10K2.t7319 from rfl, allE_node, rows7318, irow7311, rows7319]
  all_goals rfl

theorem atot7311 : totK PA10K2 A10K2.u7311 = [0, 0, 0, 1023560635464, 3785544335592, 3839361113060, 846196675594, 44238351179, 0, 0] := by
  rw [show A10K2.u7311 = KTree.node A10K2.t7318 (nat_lit 119712035) (nat_lit 10160992118) (nat_lit 0) A10K2.t7319 from rfl, totK_node, tot7318, tot7319]
  decide +kernel

theorem arows7314 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7314 = true := by
  rw [show A10K2.u7314 = KTree.node A10K2.t7320 (nat_lit 119723172) (nat_lit 13352547187) (nat_lit 0) A10K2.t7321 from rfl, allE_node, rows7320, irow7314, rows7321]
  all_goals rfl

theorem atot7314 : totK PA10K2 A10K2.u7314 = [0, 0, 310758541238, 1188825499157, 2584777633521, 3430829468267, 1496989635316, 199438448629, 5976421810, 0] := by
  rw [show A10K2.u7314 = KTree.node A10K2.t7320 (nat_lit 119723172) (nat_lit 13352547187) (nat_lit 0) A10K2.t7321 from rfl, totK_node, tot7320, tot7321]
  decide +kernel

theorem arows7315 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7315 = true := by
  rw [show A10K2.u7315 = KTree.node A10K2.t7322 (nat_lit 119737918) (nat_lit 15915774383) (nat_lit 0) A10K2.t7323 from rfl, allE_node, rows7322, irow7315, rows7323]
  all_goals rfl

theorem atot7315 : totK PA10K2 A10K2.u7315 = [0, 0, 499725545621, 2516242630619, 4064969344825, 2299264488110, 435717617074, 25351274858, 0, 0] := by
  rw [show A10K2.u7315 = KTree.node A10K2.t7322 (nat_lit 119737918) (nat_lit 15915774383) (nat_lit 0) A10K2.t7323 from rfl, totK_node, tot7322, tot7323]
  decide +kernel

theorem arows7317 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7317 = true := by
  rw [show A10K2.u7317 = KTree.node A10K2.t7324 (nat_lit 119745599) (nat_lit 14210038504) (nat_lit 0) A10K2.t7325 from rfl, allE_node, rows7324, irow7317, rows7325]
  all_goals rfl

theorem atot7317 : totK PA10K2 A10K2.u7317 = [0, 0, 512353472697, 2544658340016, 4243724564962, 2532576349972, 419315889546, 12840446565, 0, 0] := by
  rw [show A10K2.u7317 = KTree.node A10K2.t7324 (nat_lit 119745599) (nat_lit 14210038504) (nat_lit 0) A10K2.t7325 from rfl, totK_node, tot7324, tot7325]
  decide +kernel

theorem arows7318 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7318 = true := by
  rw [show A10K2.u7318 = KTree.node A10K2.t7326 (nat_lit 119760279) (nat_lit 14384969889) (nat_lit 0) A10K2.t7327 from rfl, allE_node, rows7326, irow7318, rows7327]
  all_goals rfl

theorem atot7318 : totK PA10K2 A10K2.u7318 = [0, 0, 845700278790, 3324951591030, 4162237475527, 1637116370598, 127037332594, 0, 0, 0] := by
  rw [show A10K2.u7318 = KTree.node A10K2.t7326 (nat_lit 119760279) (nat_lit 14384969889) (nat_lit 0) A10K2.t7327 from rfl, totK_node, tot7326, tot7327]
  decide +kernel

theorem arows7323 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7323 = true := by
  rw [show A10K2.u7323 = KTree.node A10K2.t7328 (nat_lit 119766067) (nat_lit 6921941572) (nat_lit 0) A10K2.t7329 from rfl, allE_node, rows7328, irow7323, rows7329]
  all_goals rfl

theorem atot7323 : totK PA10K2 A10K2.u7323 = [0, 0, 0, 1153653108161, 3939172598067, 3856266041782, 1062911088796, 62725267482, 0, 0] := by
  rw [show A10K2.u7323 = KTree.node A10K2.t7328 (nat_lit 119766067) (nat_lit 6921941572) (nat_lit 0) A10K2.t7329 from rfl, totK_node, tot7328, tot7329]
  decide +kernel

theorem arows7324 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7324 = true := by
  rw [show A10K2.u7324 = KTree.node A10K2.t7330 (nat_lit 119770661) (nat_lit 5777822655) (nat_lit 0) A10K2.t7331 from rfl, allE_node, rows7330, irow7324, rows7331]
  all_goals rfl

theorem atot7324 : totK PA10K2 A10K2.u7324 = [0, 0, 0, 499628035384, 2606546862903, 4196792228125, 2150744823174, 296215634123, 6904928264, 0] := by
  rw [show A10K2.u7324 = KTree.node A10K2.t7330 (nat_lit 119770661) (nat_lit 5777822655) (nat_lit 0) A10K2.t7331 from rfl, totK_node, tot7330, tot7331]
  decide +kernel

theorem arows7326 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7326 = true := by
  rw [show A10K2.u7326 = KTree.node A10K2.t7332 (nat_lit 119778757) (nat_lit 1544250288) (nat_lit 0) A10K2.t7333 from rfl, allE_node, rows7332, irow7326, rows7333]
  all_goals rfl

theorem atot7326 : totK PA10K2 A10K2.u7326 = [0, 0, 0, 894114717497, 3438019120734, 4177354778584, 1568964425977, 122557863561, 0, 0] := by
  rw [show A10K2.u7326 = KTree.node A10K2.t7332 (nat_lit 119778757) (nat_lit 1544250288) (nat_lit 0) A10K2.t7333 from rfl, totK_node, tot7332, tot7333]
  decide +kernel

theorem arows7327 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7327 = true := by
  rw [show A10K2.u7327 = KTree.node A10K2.t7334 (nat_lit 119795639) (nat_lit 15196976937) (nat_lit 0) A10K2.t7335 from rfl, allE_node, rows7334, irow7327, rows7335]
  all_goals rfl

theorem atot7327 : totK PA10K2 A10K2.u7327 = [0, 0, 0, 462103283522, 2634968466381, 4251413196300, 2291966480681, 297863468931, 6066958478, 0] := by
  rw [show A10K2.u7327 = KTree.node A10K2.t7334 (nat_lit 119795639) (nat_lit 15196976937) (nat_lit 0) A10K2.t7335 from rfl, totK_node, tot7334, tot7335]
  decide +kernel

theorem arows7330 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7330 = true := by
  rw [show A10K2.u7330 = KTree.node A10K2.t7336 (nat_lit 119800763) (nat_lit 5470977822) (nat_lit 0) A10K2.t7337 from rfl, allE_node, rows7336, irow7330, rows7337]
  all_goals rfl

theorem atot7330 : totK PA10K2 A10K2.u7330 = [0, 0, 0, 862503187692, 3105655330210, 3670264673305, 1699914478881, 398641288479, 28503589898, 0] := by
  rw [show A10K2.u7330 = KTree.node A10K2.t7336 (nat_lit 119800763) (nat_lit 5470977822) (nat_lit 0) A10K2.t7337 from rfl, totK_node, tot7336, tot7337]
  decide +kernel

theorem arows7331 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7331 = true := by
  rw [show A10K2.u7331 = KTree.node A10K2.t7338 (nat_lit 119806305) (nat_lit 8969180636) (nat_lit 0) A10K2.t7339 from rfl, allE_node, rows7338, irow7331, rows7339]
  all_goals rfl

theorem atot7331 : totK PA10K2 A10K2.u7331 = [0, 0, 0, 292562553233, 1878290139851, 3906268471123, 2796857668508, 588978261493, 30831673886, 0] := by
  rw [show A10K2.u7331 = KTree.node A10K2.t7338 (nat_lit 119806305) (nat_lit 8969180636) (nat_lit 0) A10K2.t7339 from rfl, totK_node, tot7338, tot7339]
  decide +kernel

theorem arows7333 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7333 = true := by
  rw [show A10K2.u7333 = KTree.node A10K2.t7340 (nat_lit 119820545) (nat_lit 10329861105) (nat_lit 0) A10K2.t7341 from rfl, allE_node, rows7340, irow7333, rows7341]
  all_goals rfl

theorem atot7333 : totK PA10K2 A10K2.u7333 = [0, 0, 0, 574525067762, 2635384013624, 3858282281779, 1701528145885, 211600369819, 5705019915, 0] := by
  rw [show A10K2.u7333 = KTree.node A10K2.t7340 (nat_lit 119820545) (nat_lit 10329861105) (nat_lit 0) A10K2.t7341 from rfl, totK_node, tot7340, tot7341]
  decide +kernel

theorem arows7334 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7334 = true := by
  rw [show A10K2.u7334 = KTree.node A10K2.t7342 (nat_lit 119828008) (nat_lit 12032440975) (nat_lit 0) A10K2.t7343 from rfl, allE_node, rows7342, irow7334, rows7343]
  all_goals rfl

theorem atot7334 : totK PA10K2 A10K2.u7334 = [0, 0, 0, 592348102083, 2816338167727, 4219601095882, 2132836574705, 311993985934, 6853348008, 0] := by
  rw [show A10K2.u7334 = KTree.node A10K2.t7342 (nat_lit 119828008) (nat_lit 12032440975) (nat_lit 0) A10K2.t7343 from rfl, totK_node, tot7342, tot7343]
  decide +kernel

theorem arows7338 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7338 = true := by
  rw [show A10K2.u7338 = KTree.node A10K2.t7344 (nat_lit 119833207) (nat_lit 10189420915) (nat_lit 0) A10K2.t7345 from rfl, allE_node, rows7344, irow7338, rows7345]
  all_goals rfl

theorem atot7338 : totK PA10K2 A10K2.u7338 = [0, 0, 0, 0, 1061021783958, 3808058438163, 3704367881769, 933549086741, 59400237386, 0] := by
  rw [show A10K2.u7338 = KTree.node A10K2.t7344 (nat_lit 119833207) (nat_lit 10189420915) (nat_lit 0) A10K2.t7345 from rfl, totK_node, tot7344, tot7345]
  decide +kernel

theorem arows7339 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7339 = true := by
  rw [show A10K2.u7339 = KTree.node A10K2.t7346 (nat_lit 119839757) (nat_lit 5409365601) (nat_lit 0) A10K2.t7347 from rfl, allE_node, rows7346, irow7339, rows7347]
  all_goals rfl

theorem atot7339 : totK PA10K2 A10K2.u7339 = [0, 0, 0, 0, 505902306987, 2496670543426, 3956184959758, 2135901091633, 324558235390, 7903172220] := by
  rw [show A10K2.u7339 = KTree.node A10K2.t7346 (nat_lit 119839757) (nat_lit 5409365601) (nat_lit 0) A10K2.t7347 from rfl, totK_node, tot7346, tot7347]
  decide +kernel

theorem arows7341 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7341 = true := by
  rw [show A10K2.u7341 = KTree.node A10K2.t7348 (nat_lit 119858362) (nat_lit 12385941787) (nat_lit 0) A10K2.t7349 from rfl, allE_node, rows7348, irow7341, rows7349]
  all_goals rfl

theorem atot7341 : totK PA10K2 A10K2.u7341 = [0, 0, 0, 306117011728, 1735743202092, 3722394605392, 3089636644001, 755167702658, 44519063297, 0] := by
  rw [show A10K2.u7341 = KTree.node A10K2.t7348 (nat_lit 119858362) (nat_lit 12385941787) (nat_lit 0) A10K2.t7349 from rfl, totK_node, tot7348, tot7349]
  decide +kernel

theorem arows7342 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7342 = true := by
  rw [show A10K2.u7342 = KTree.node A10K2.t7350 (nat_lit 119934408) (nat_lit 13975665971) (nat_lit 0) A10K2.t7351 from rfl, allE_node, rows7350, irow7342, rows7351]
  all_goals rfl

theorem atot7342 : totK PA10K2 A10K2.u7342 = [0, 0, 0, 483587366435, 2584460451344, 4200357337187, 2015170028601, 240032197543, 5300418178, 0] := by
  rw [show A10K2.u7342 = KTree.node A10K2.t7350 (nat_lit 119934408) (nat_lit 13975665971) (nat_lit 0) A10K2.t7351 from rfl, totK_node, tot7350, tot7351]
  decide +kernel

theorem arows7345 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7345 = true := by
  rw [show A10K2.u7345 = KTree.node A10K2.t7352 (nat_lit 119947321) (nat_lit 7204189479) (nat_lit 0) A10K2.t7353 from rfl, allE_node, rows7352, irow7345, rows7353]
  all_goals rfl

theorem atot7345 : totK PA10K2 A10K2.u7345 = [0, 0, 0, 871781113126, 3157599938302, 3780373492732, 1465428587822, 181623743371, 5460492893, 0] := by
  rw [show A10K2.u7345 = KTree.node A10K2.t7352 (nat_lit 119947321) (nat_lit 7204189479) (nat_lit 0) A10K2.t7353 from rfl, totK_node, tot7352, tot7353]
  decide +kernel

theorem arows7346 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7346 = true := by
  rw [show A10K2.u7346 = KTree.node A10K2.t7354 (nat_lit 119953573) (nat_lit 7333572875) (nat_lit 0) A10K2.t7355 from rfl, allE_node, rows7354, irow7346, rows7355]
  all_goals rfl

theorem atot7346 : totK PA10K2 A10K2.u7346 = [0, 0, 0, 462168327342, 2592388702217, 4170743325786, 1911871593950, 221598459622, 6354482628, 0] := by
  rw [show A10K2.u7346 = KTree.node A10K2.t7354 (nat_lit 119953573) (nat_lit 7333572875) (nat_lit 0) A10K2.t7355 from rfl, totK_node, tot7354, tot7355]
  decide +kernel

theorem arows7348 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7348 = true := by
  rw [show A10K2.u7348 = KTree.node A10K2.t7356 (nat_lit 120000516) (nat_lit 11952560992) (nat_lit 0) A10K2.t7357 from rfl, allE_node, rows7356, irow7348, rows7357]
  all_goals rfl

theorem atot7348 : totK PA10K2 A10K2.u7348 = [0, 0, 0, 455118883607, 2541203592993, 4263093041397, 2196970119173, 336644096200, 13360781053, 0] := by
  rw [show A10K2.u7348 = KTree.node A10K2.t7356 (nat_lit 120000516) (nat_lit 11952560992) (nat_lit 0) A10K2.t7357 from rfl, totK_node, tot7356, tot7357]
  decide +kernel

theorem arows7349 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7349 = true := by
  rw [show A10K2.u7349 = KTree.node A10K2.t7358 (nat_lit 120021070) (nat_lit 10904956324) (nat_lit 0) A10K2.t7359 from rfl, allE_node, rows7358, irow7349, rows7359]
  all_goals rfl

theorem atot7349 : totK PA10K2 A10K2.u7349 = [0, 0, 0, 1175817307097, 3864752840356, 3829523223821, 1287592077692, 105046128051, 0, 0] := by
  rw [show A10K2.u7349 = KTree.node A10K2.t7358 (nat_lit 120021070) (nat_lit 10904956324) (nat_lit 0) A10K2.t7359 from rfl, totK_node, tot7358, tot7359]
  decide +kernel

theorem arows7355 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7355 = true := by
  rw [show A10K2.u7355 = KTree.node A10K2.t7360 (nat_lit 120025714) (nat_lit 7792494334) (nat_lit 0) A10K2.t7361 from rfl, allE_node, rows7360, irow7355, rows7361]
  all_goals rfl

theorem atot7355 : totK PA10K2 A10K2.u7355 = [0, 0, 176847655326, 561303166672, 1894206412741, 3871677848231, 2859487138930, 632814783984, 35503361870, 0] := by
  rw [show A10K2.u7355 = KTree.node A10K2.t7360 (nat_lit 120025714) (nat_lit 7792494334) (nat_lit 0) A10K2.t7361 from rfl, totK_node, tot7360, tot7361]
  decide +kernel

theorem arows7356 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7356 = true := by
  rw [show A10K2.u7356 = KTree.node A10K2.t7362 (nat_lit 120589321) (nat_lit 9732766126) (nat_lit 0) A10K2.t7363 from rfl, allE_node, rows7362, irow7356, rows7363]
  all_goals rfl

theorem atot7356 : totK PA10K2 A10K2.u7356 = [0, 0, 661944769737, 2986498638224, 4044771309983, 1728096753273, 235669093802, 14945844243, 0, 0] := by
  rw [show A10K2.u7356 = KTree.node A10K2.t7362 (nat_lit 120589321) (nat_lit 9732766126) (nat_lit 0) A10K2.t7363 from rfl, totK_node, tot7362, tot7363]
  decide +kernel

theorem arows7358 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7358 = true := by
  rw [show A10K2.u7358 = KTree.node A10K2.t7364 (nat_lit 120602683) (nat_lit 1696446081) (nat_lit 0) A10K2.t7365 from rfl, allE_node, rows7364, irow7358, rows7365]
  all_goals rfl

theorem atot7358 : totK PA10K2 A10K2.u7358 = [0, 0, 594333390776, 2511273528485, 3790035414352, 2194611905540, 395041840578, 15885829643, 0, 0] := by
  rw [show A10K2.u7358 = KTree.node A10K2.t7364 (nat_lit 120602683) (nat_lit 1696446081) (nat_lit 0) A10K2.t7365 from rfl, totK_node, tot7364, tot7365]
  decide +kernel

theorem arows7359 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7359 = true := by
  rw [show A10K2.u7359 = KTree.node A10K2.t7366 (nat_lit 120608869) (nat_lit 7128301732) (nat_lit 0) A10K2.t7367 from rfl, allE_node, rows7366, irow7359, rows7367]
  all_goals rfl

theorem atot7359 : totK PA10K2 A10K2.u7359 = [0, 0, 443379202432, 2545138687070, 4182636593452, 2049360889366, 240611254028, 6354482628, 0, 0] := by
  rw [show A10K2.u7359 = KTree.node A10K2.t7366 (nat_lit 120608869) (nat_lit 7128301732) (nat_lit 0) A10K2.t7367 from rfl, totK_node, tot7366, tot7367]
  decide +kernel

theorem arows7362 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7362 = true := by
  rw [show A10K2.u7362 = KTree.node A10K2.t7368 (nat_lit 120615487) (nat_lit 10366022413) (nat_lit 0) A10K2.t7369 from rfl, allE_node, rows7368, irow7362, rows7369]
  all_goals rfl

theorem atot7362 : totK PA10K2 A10K2.u7362 = [0, 0, 295757175837, 1991156760307, 4287770287631, 3094316946084, 517965394202, 12746179907, 0, 0] := by
  rw [show A10K2.u7362 = KTree.node A10K2.t7368 (nat_lit 120615487) (nat_lit 10366022413) (nat_lit 0) A10K2.t7369 from rfl, totK_node, tot7368, tot7369]
  decide +kernel

theorem arows7363 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7363 = true := by
  rw [show A10K2.u7363 = KTree.node A10K2.t7370 (nat_lit 120622550) (nat_lit 15310186921) (nat_lit 0) A10K2.t7371 from rfl, allE_node, rows7370, irow7363, rows7371]
  all_goals rfl

theorem atot7363 : totK PA10K2 A10K2.u7363 = [0, 0, 0, 977760188652, 3715588537894, 3888552834275, 988617713915, 63728309746, 0, 0] := by
  rw [show A10K2.u7363 = KTree.node A10K2.t7370 (nat_lit 120622550) (nat_lit 15310186921) (nat_lit 0) A10K2.t7371 from rfl, totK_node, tot7370, tot7371]
  decide +kernel

theorem arows7365 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7365 = true := by
  rw [show A10K2.u7365 = KTree.node A10K2.t7372 (nat_lit 120640804) (nat_lit 13973624068) (nat_lit 0) A10K2.t7373 from rfl, allE_node, rows7372, irow7365, rows7373]
  all_goals rfl

theorem atot7365 : totK PA10K2 A10K2.u7365 = [0, 0, 0, 583611352284, 2781770300554, 4092726378466, 1671723095927, 206102663612, 5546304973, 0] := by
  rw [show A10K2.u7365 = KTree.node A10K2.t7372 (nat_lit 120640804) (nat_lit 13973624068) (nat_lit 0) A10K2.t7373 from rfl, totK_node, tot7372, tot7373]
  decide +kernel

theorem arows7366 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7366 = true := by
  rw [show A10K2.u7366 = KTree.node A10K2.t7374 (nat_lit 120719360) (nat_lit 15386734203) (nat_lit 0) A10K2.t7375 from rfl, allE_node, rows7374, irow7366, rows7375]
  all_goals rfl

theorem atot7366 : totK PA10K2 A10K2.u7366 = [0, 0, 762344704339, 3183303403117, 4120149675996, 1667588973927, 142485941233, 0, 0, 0] := by
  rw [show A10K2.u7366 = KTree.node A10K2.t7374 (nat_lit 120719360) (nat_lit 15386734203) (nat_lit 0) A10K2.t7375 from rfl, totK_node, tot7374, tot7375]
  decide +kernel

theorem arows7370 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7370 = true := by
  rw [show A10K2.u7370 = KTree.node A10K2.t7376 (nat_lit 120724323) (nat_lit 5167329717) (nat_lit 0) A10K2.t7377 from rfl, allE_node, rows7376, irow7370, rows7377]
  all_goals rfl

theorem atot7370 : totK PA10K2 A10K2.u7370 = [0, 0, 500575738652, 2192283534665, 3768014770734, 2536391143517, 499153912094, 30831673886, 0, 0] := by
  rw [show A10K2.u7370 = KTree.node A10K2.t7376 (nat_lit 120724323) (nat_lit 5167329717) (nat_lit 0) A10K2.t7377 from rfl, totK_node, tot7376, tot7377]
  decide +kernel

theorem arows7371 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7371 = true := by
  rw [show A10K2.u7371 = KTree.node A10K2.t7378 (nat_lit 120731913) (nat_lit 8538405892) (nat_lit 0) A10K2.t7379 from rfl, allE_node, rows7378, irow7371, rows7379]
  all_goals rfl

theorem atot7371 : totK PA10K2 A10K2.u7371 = [0, 0, 423790827876, 2325578427077, 3955695785778, 2380006619687, 375404178605, 11427838733, 0, 0] := by
  rw [show A10K2.u7371 = KTree.node A10K2.t7378 (nat_lit 120731913) (nat_lit 8538405892) (nat_lit 0) A10K2.t7379 from rfl, totK_node, tot7378, tot7379]
  decide +kernel

theorem arows7373 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7373 = true := by
  rw [show A10K2.u7373 = KTree.node A10K2.t7380 (nat_lit 120737829) (nat_lit 7133953813) (nat_lit 0) A10K2.t7381 from rfl, allE_node, rows7380, irow7373, rows7381]
  all_goals rfl

theorem atot7373 : totK PA10K2 A10K2.u7373 = [0, 0, 431985945682, 2531847081486, 4232720134421, 2022670176912, 181897378426, 0, 0, 0] := by
  rw [show A10K2.u7373 = KTree.node A10K2.t7380 (nat_lit 120737829) (nat_lit 7133953813) (nat_lit 0) A10K2.t7381 from rfl, totK_node, tot7380, tot7381]
  decide +kernel

theorem arows7374 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7374 = true := by
  rw [show A10K2.u7374 = KTree.node A10K2.t7382 (nat_lit 120752490) (nat_lit 9580055931) (nat_lit 0) A10K2.t7383 from rfl, allE_node, rows7382, irow7374, rows7383]
  all_goals rfl

theorem atot7374 : totK PA10K2 A10K2.u7374 = [0, 0, 0, 1040290194111, 3833101309981, 3873669469503, 849878530673, 43869152019, 0, 0] := by
  rw [show A10K2.u7374 = KTree.node A10K2.t7382 (nat_lit 120752490) (nat_lit 9580055931) (nat_lit 0) A10K2.t7383 from rfl, totK_node, tot7382, tot7383]
  decide +kernel

theorem arows7377 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7377 = true := by
  rw [show A10K2.u7377 = KTree.node A10K2.t7384 (nat_lit 120767266) (nat_lit 11045330773) (nat_lit 0) A10K2.t7385 from rfl, allE_node, rows7384, irow7377, rows7385]
  all_goals rfl

theorem atot7377 : totK PA10K2 A10K2.u7377 = [0, 0, 0, 1097154129097, 3874194170427, 3664066315704, 744821928184, 36992254861, 0, 0] := by
  rw [show A10K2.u7377 = KTree.node A10K2.t7384 (nat_lit 120767266) (nat_lit 11045330773) (nat_lit 0) A10K2.t7385 from rfl, totK_node, tot7384, tot7385]
  decide +kernel

theorem arows7378 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7378 = true := by
  rw [show A10K2.u7378 = KTree.node A10K2.t7386 (nat_lit 120773290) (nat_lit 11831635078) (nat_lit 0) A10K2.t7387 from rfl, allE_node, rows7386, irow7378, rows7387]
  all_goals rfl

theorem atot7378 : totK PA10K2 A10K2.u7378 = [0, 0, 540022072669, 1706463564108, 2421579543319, 2923992948476, 1488671711392, 215242118554, 6354482628, 0] := by
  rw [show A10K2.u7378 = KTree.node A10K2.t7386 (nat_lit 120773290) (nat_lit 11831635078) (nat_lit 0) A10K2.t7387 from rfl, totK_node, tot7386, tot7387]
  decide +kernel

theorem arows7380 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7380 = true := by
  rw [show A10K2.u7380 = KTree.node A10K2.t7388 (nat_lit 121114901) (nat_lit 6333825335) (nat_lit 0) A10K2.t7389 from rfl, allE_node, rows7388, irow7380, rows7389]
  all_goals rfl

theorem atot7380 : totK PA10K2 A10K2.u7380 = [0, 0, 295901161011, 1995370221090, 3989078431037, 2682888732814, 565436021739, 30831673886, 0, 0] := by
  rw [show A10K2.u7380 = KTree.node A10K2.t7388 (nat_lit 121114901) (nat_lit 6333825335) (nat_lit 0) A10K2.t7389 from rfl, totK_node, tot7388, tot7389]
  decide +kernel

theorem arows7381 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7381 = true := by
  rw [show A10K2.u7381 = KTree.node A10K2.t7390 (nat_lit 121129237) (nat_lit 7051909534) (nat_lit 0) A10K2.t7391 from rfl, allE_node, rows7390, irow7381, rows7391]
  all_goals rfl

theorem atot7381 : totK PA10K2 A10K2.u7381 = [0, 0, 536206938430, 2607415397459, 4037406676720, 1983764078358, 259588908267, 5976421810, 0, 0] := by
  rw [show A10K2.u7381 = KTree.node A10K2.t7390 (nat_lit 121129237) (nat_lit 7051909534) (nat_lit 0) A10K2.t7391 from rfl, totK_node, tot7390, tot7391]
  decide +kernel

theorem arows7386 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7386 = true := by
  rw [show A10K2.u7386 = KTree.node A10K2.t7392 (nat_lit 121138220) (nat_lit 8107194863) (nat_lit 0) A10K2.t7393 from rfl, allE_node, rows7392, irow7386, rows7393]
  all_goals rfl

theorem atot7386 : totK PA10K2 A10K2.u7386 = [0, 0, 793449030898, 3301668047036, 4229629063363, 1723185940592, 163397852721, 0, 0, 0] := by
  rw [show A10K2.u7386 = KTree.node A10K2.t7392 (nat_lit 121138220) (nat_lit 8107194863) (nat_lit 0) A10K2.t7393 from rfl, totK_node, tot7392, tot7393]
  decide +kernel

theorem arows7387 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7387 = true := by
  rw [show A10K2.u7387 = KTree.node A10K2.t7394 (nat_lit 121142884) (nat_lit 6695884084) (nat_lit 0) A10K2.t7395 from rfl, allE_node, rows7394, irow7387, rows7395]
  all_goals rfl

theorem atot7387 : totK PA10K2 A10K2.u7387 = [0, 0, 0, 959208588318, 3613877687944, 4125216961194, 1279516359354, 88375597180, 0, 0] := by
  rw [show A10K2.u7387 = KTree.node A10K2.t7394 (nat_lit 121142884) (nat_lit 6695884084) (nat_lit 0) A10K2.t7395 from rfl, totK_node, tot7394, tot7395]
  decide +kernel

theorem arows7389 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7389 = true := by
  rw [show A10K2.u7389 = KTree.node A10K2.t7396 (nat_lit 121147463) (nat_lit 10923059249) (nat_lit 0) A10K2.t7397 from rfl, allE_node, rows7396, irow7389, rows7397]
  all_goals rfl

theorem atot7389 : totK PA10K2 A10K2.u7389 = [0, 0, 0, 400811964952, 2310403924875, 4009277238277, 2329271371728, 406622604146, 13364899180, 0] := by
  rw [show A10K2.u7389 = KTree.node A10K2.t7396 (nat_lit 121147463) (nat_lit 10923059249) (nat_lit 0) A10K2.t7397 from rfl, totK_node, tot7396, tot7397]
  decide +kernel

theorem arows7390 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7390 = true := by
  rw [show A10K2.u7390 = KTree.node A10K2.t7398 (nat_lit 121162253) (nat_lit 5801448251) (nat_lit 0) A10K2.t7399 from rfl, allE_node, rows7398, irow7390, rows7399]
  all_goals rfl

theorem atot7390 : totK PA10K2 A10K2.u7390 = [0, 0, 0, 1019343946839, 3723661491299, 3869380521962, 1075866090689, 73086778719, 0, 0] := by
  rw [show A10K2.u7390 = KTree.node A10K2.t7398 (nat_lit 121162253) (nat_lit 5801448251) (nat_lit 0) A10K2.t7399 from rfl, totK_node, tot7398, tot7399]
  decide +kernel

theorem arows7393 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7393 = true := by
  rw [show A10K2.u7393 = KTree.node A10K2.t7400 (nat_lit 121185671) (nat_lit 13992010260) (nat_lit 0) A10K2.t7401 from rfl, allE_node, rows7400, irow7393, rows7401]
  all_goals rfl

theorem atot7393 : totK PA10K2 A10K2.u7393 = [0, 0, 779827310996, 2884211232233, 3577615796671, 2155317378331, 687762357698, 57270499718, 0, 0] := by
  rw [show A10K2.u7393 = KTree.node A10K2.t7400 (nat_lit 121185671) (nat_lit 13992010260) (nat_lit 0) A10K2.t7401 from rfl, totK_node, tot7400, tot7401]
  decide +kernel

theorem arows7394 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7394 = true := by
  rw [show A10K2.u7394 = KTree.node A10K2.t7402 (nat_lit 121190646) (nat_lit 14885090250) (nat_lit 0) A10K2.t7403 from rfl, allE_node, rows7402, irow7394, rows7403]
  all_goals rfl

theorem atot7394 : totK PA10K2 A10K2.u7394 = [0, 0, 331085587170, 2180641298804, 4322543264088, 2873112790674, 493369763470, 13576218110, 0, 0] := by
  rw [show A10K2.u7394 = KTree.node A10K2.t7402 (nat_lit 121190646) (nat_lit 14885090250) (nat_lit 0) A10K2.t7403 from rfl, totK_node, tot7402, tot7403]
  decide +kernel

theorem arows7396 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7396 = true := by
  rw [show A10K2.u7396 = KTree.node A10K2.t7404 (nat_lit 121204622) (nat_lit 15075358843) (nat_lit 0) A10K2.t7405 from rfl, allE_node, rows7404, irow7396, rows7405]
  all_goals rfl

theorem atot7396 : totK PA10K2 A10K2.u7396 = [0, 0, 480625918787, 2441697263646, 4205281781985, 2704276114666, 472106991117, 13548089516, 0, 0] := by
  rw [show A10K2.u7396 = KTree.node A10K2.t7404 (nat_lit 121204622) (nat_lit 15075358843) (nat_lit 0) A10K2.t7405 from rfl, totK_node, tot7404, tot7405]
  decide +kernel

theorem arows7397 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7397 = true := by
  rw [show A10K2.u7397 = KTree.node A10K2.t7406 (nat_lit 121218526) (nat_lit 14881596446) (nat_lit 0) A10K2.t7407 from rfl, allE_node, rows7406, irow7397, rows7407]
  all_goals rfl

theorem atot7397 : totK PA10K2 A10K2.u7397 = [0, 0, 0, 1097847239553, 3835790591084, 4014950273391, 1184678909155, 69642194947, 0, 0] := by
  rw [show A10K2.u7397 = KTree.node A10K2.t7406 (nat_lit 121218526) (nat_lit 14881596446) (nat_lit 0) A10K2.t7407 from rfl, totK_node, tot7406, tot7407]
  decide +kernel

theorem arows7401 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7401 = true := by
  rw [show A10K2.u7401 = KTree.node A10K2.t7408 (nat_lit 121224703) (nat_lit 11013672994) (nat_lit 0) A10K2.t7409 from rfl, allE_node, rows7408, irow7401, rows7409]
  all_goals rfl

theorem atot7401 : totK PA10K2 A10K2.u7401 = [0, 0, 0, 597805554384, 2915899165499, 4266824227791, 2047193809565, 256522054045, 7380853412, 0] := by
  rw [show A10K2.u7401 = KTree.node A10K2.t7408 (nat_lit 121224703) (nat_lit 11013672994) (nat_lit 0) A10K2.t7409 from rfl, totK_node, tot7408, tot7409]
  decide +kernel

theorem arows7402 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7402 = true := by
  rw [show A10K2.u7402 = KTree.node A10K2.t7410 (nat_lit 121307690) (nat_lit 4178043730) (nat_lit 0) A10K2.t7411 from rfl, allE_node, rows7410, irow7402, rows7411]
  all_goals rfl

theorem atot7402 : totK PA10K2 A10K2.u7402 = [0, 0, 777824669607, 2896425809222, 3612153531396, 2023111043305, 589646968302, 50555834002, 0, 0] := by
  rw [show A10K2.u7402 = KTree.node A10K2.t7410 (nat_lit 121307690) (nat_lit 4178043730) (nat_lit 0) A10K2.t7411 from rfl, totK_node, tot7410, tot7411]
  decide +kernel

theorem arows7404 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7404 = true := by
  rw [show A10K2.u7404 = KTree.node A10K2.t7412 (nat_lit 121313793) (nat_lit 10478560941) (nat_lit 0) A10K2.t7413 from rfl, allE_node, rows7412, irow7404, rows7413]
  all_goals rfl

theorem atot7404 : totK PA10K2 A10K2.u7404 = [0, 0, 324317460390, 2016094178091, 4168856912678, 2806054776962, 514764554631, 18429085292, 0, 0] := by
  rw [show A10K2.u7404 = KTree.node A10K2.t7412 (nat_lit 121313793) (nat_lit 10478560941) (nat_lit 0) A10K2.t7413 from rfl, totK_node, tot7412, tot7413]
  decide +kernel

theorem arows7405 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7405 = true := by
  rw [show A10K2.u7405 = KTree.node A10K2.t7414 (nat_lit 121320851) (nat_lit 10760725755) (nat_lit 0) A10K2.t7415 from rfl, allE_node, rows7414, irow7405, rows7415]
  all_goals rfl

theorem atot7405 : totK PA10K2 A10K2.u7405 = [0, 0, 529346169851, 2581508503060, 4126899699188, 2516170093831, 414402364455, 12692412833, 0, 0] := by
  rw [show A10K2.u7405 = KTree.node A10K2.t7414 (nat_lit 121320851) (nat_lit 10760725755) (nat_lit 0) A10K2.t7415 from rfl, totK_node, tot7414, tot7415]
  decide +kernel

theorem arows7408 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7408 = true := by
  rw [show A10K2.u7408 = KTree.node A10K2.t7416 (nat_lit 121334884) (nat_lit 7416072308) (nat_lit 0) A10K2.t7417 from rfl, allE_node, rows7416, irow7408, rows7417]
  all_goals rfl

theorem atot7408 : totK PA10K2 A10K2.u7408 = [0, 0, 715278061713, 3084047831493, 4264014443166, 1856726585435, 174252453633, 0, 0, 0] := by
  rw [show A10K2.u7408 = KTree.node A10K2.t7416 (nat_lit 121334884) (nat_lit 7416072308) (nat_lit 0) A10K2.t7417 from rfl, totK_node, tot7416, tot7417]
  decide +kernel

theorem arows7409 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7409 = true := by
  rw [show A10K2.u7409 = KTree.node A10K2.t7418 (nat_lit 121339396) (nat_lit 8569531780) (nat_lit 0) A10K2.t7419 from rfl, allE_node, rows7418, irow7409, rows7419]
  all_goals rfl

theorem atot7409 : totK PA10K2 A10K2.u7409 = [0, 0, 0, 1000216828559, 3610713391397, 3986988334188, 1258368300373, 81490929768, 0, 0] := by
  rw [show A10K2.u7409 = KTree.node A10K2.t7418 (nat_lit 121339396) (nat_lit 8569531780) (nat_lit 0) A10K2.t7419 from rfl, totK_node, tot7418, tot7419]
  decide +kernel

theorem arows7411 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7411 = true := by
  rw [show A10K2.u7411 = KTree.node A10K2.t7420 (nat_lit 121344106) (nat_lit 3274740095) (nat_lit 0) A10K2.t7421 from rfl, allE_node, rows7420, irow7411, rows7421]
  all_goals rfl

theorem atot7411 : totK PA10K2 A10K2.u7411 = [0, 0, 0, 487245983729, 2550663404392, 4202095312026, 2280982818889, 307011986866, 6904928264, 0] := by
  rw [show A10K2.u7411 = KTree.node A10K2.t7420 (nat_lit 121344106) (nat_lit 3274740095) (nat_lit 0) A10K2.t7421 from rfl, totK_node, tot7420, tot7421]
  decide +kernel

theorem arows7412 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7412 = true := by
  rw [show A10K2.u7412 = KTree.node A10K2.t7422 (nat_lit 121351748) (nat_lit 7193775202) (nat_lit 0) A10K2.t7423 from rfl, allE_node, rows7422, irow7412, rows7423]
  all_goals rfl

theorem atot7412 : totK PA10K2 A10K2.u7412 = [0, 0, 0, 572137771939, 2895977250338, 4265788548387, 2090232322145, 254685126899, 6766355402, 0] := by
  rw [show A10K2.u7412 = KTree.node A10K2.t7422 (nat_lit 121351748) (nat_lit 7193775202) (nat_lit 0) A10K2.t7423 from rfl, totK_node, tot7422, tot7423]
  decide +kernel

theorem arows7420 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7420 = true := by
  rw [show A10K2.u7420 = KTree.node A10K2.t7424 (nat_lit 121366180) (nat_lit 8328657230) (nat_lit 0) A10K2.t7425 from rfl, allE_node, rows7424, irow7420, rows7425]
  all_goals rfl

theorem atot7420 : totK PA10K2 A10K2.u7420 = [0, 0, 0, 880779957843, 3419992088967, 4072490379659, 1486672452177, 113088615740, 0, 0] := by
  rw [show A10K2.u7420 = KTree.node A10K2.t7424 (nat_lit 121366180) (nat_lit 8328657230) (nat_lit 0) A10K2.t7425 from rfl, totK_node, tot7424, tot7425]
  decide +kernel

theorem arows7421 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7421 = true := by
  rw [show A10K2.u7421 = KTree.node A10K2.t7426 (nat_lit 121371796) (nat_lit 8724092396) (nat_lit 0) A10K2.t7427 from rfl, allE_node, rows7426, irow7421, rows7427]
  all_goals rfl

theorem atot7421 : totK PA10K2 A10K2.u7421 = [0, 322245181260, 977713555127, 723339976121, 859273793138, 2876689390254, 3149021294043, 908100837022, 61110126106, 0] := by
  rw [show A10K2.u7421 = KTree.node A10K2.t7426 (nat_lit 121371796) (nat_lit 8724092396) (nat_lit 0) A10K2.t7427 from rfl, totK_node, tot7426, tot7427]
  decide +kernel

theorem arows7423 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7423 = true := by
  rw [show A10K2.u7423 = KTree.node A10K2.t7428 (nat_lit 122236360) (nat_lit 11037895197) (nat_lit 0) A10K2.t7429 from rfl, allE_node, rows7428, irow7423, rows7429]
  all_goals rfl

theorem atot7423 : totK PA10K2 A10K2.u7423 = [0, 549999419660, 2554265120233, 3927214449879, 2227072001574, 431080219106, 25734533292, 0, 0, 0] := by
  rw [show A10K2.u7423 = KTree.node A10K2.t7428 (nat_lit 122236360) (nat_lit 11037895197) (nat_lit 0) A10K2.t7429 from rfl, totK_node, tot7428, tot7429]
  decide +kernel

theorem arows7424 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7424 = true := by
  rw [show A10K2.u7424 = KTree.node A10K2.t7430 (nat_lit 122241797) (nat_lit 6920038188) (nat_lit 0) A10K2.t7431 from rfl, allE_node, rows7430, irow7424, rows7431]
  all_goals rfl

theorem atot7424 : totK PA10K2 A10K2.u7424 = [0, 683621691564, 2716293478582, 3715227377651, 1973696679980, 276468280471, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u7424 = KTree.node A10K2.t7430 (nat_lit 122241797) (nat_lit 6920038188) (nat_lit 0) A10K2.t7431 from rfl, totK_node, tot7430, tot7431]
  decide +kernel

theorem arows7427 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7427 = true := by
  rw [show A10K2.u7427 = KTree.node A10K2.t7432 (nat_lit 122247509) (nat_lit 6970753704) (nat_lit 0) A10K2.t7433 from rfl, allE_node, rows7432, irow7427, rows7433]
  all_goals rfl

theorem atot7427 : totK PA10K2 A10K2.u7427 = [0, 478109165658, 2554161290131, 4165963363618, 2072468144627, 267817602942, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u7427 = KTree.node A10K2.t7432 (nat_lit 122247509) (nat_lit 6970753704) (nat_lit 0) A10K2.t7433 from rfl, totK_node, tot7432, tot7433]
  decide +kernel

theorem arows7428 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7428 = true := by
  rw [show A10K2.u7428 = KTree.node A10K2.t7434 (nat_lit 122253808) (nat_lit 13705880298) (nat_lit 0) A10K2.t7435 from rfl, allE_node, rows7434, irow7428, rows7435]
  all_goals rfl

theorem atot7428 : totK PA10K2 A10K2.u7428 = [0, 310203719009, 2111641820017, 4299591724309, 2913359420606, 505640996046, 13732569049, 0, 0, 0] := by
  rw [show A10K2.u7428 = KTree.node A10K2.t7434 (nat_lit 122253808) (nat_lit 13705880298) (nat_lit 0) A10K2.t7435 from rfl, totK_node, tot7434, tot7435]
  decide +kernel

theorem arows7430 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7430 = true := by
  rw [show A10K2.u7430 = KTree.node A10K2.t7436 (nat_lit 122267582) (nat_lit 16023159446) (nat_lit 0) A10K2.t7437 from rfl, allE_node, rows7436, irow7430, rows7437]
  all_goals rfl

theorem atot7430 : totK PA10K2 A10K2.u7430 = [0, 0, 868955275579, 3442636825702, 4048816069818, 1321999126634, 88326291749, 0, 0, 0] := by
  rw [show A10K2.u7430 = KTree.node A10K2.t7436 (nat_lit 122267582) (nat_lit 16023159446) (nat_lit 0) A10K2.t7437 from rfl, totK_node, tot7436, tot7437]
  decide +kernel

theorem arows7431 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7431 = true := by
  rw [show A10K2.u7431 = KTree.node A10K2.t7438 (nat_lit 122272087) (nat_lit 5493653933) (nat_lit 0) A10K2.t7439 from rfl, allE_node, rows7438, irow7431, rows7439]
  all_goals rfl

theorem atot7431 : totK PA10K2 A10K2.u7431 = [0, 0, 380936229014, 2002682671046, 3740748009172, 2626458325573, 570409642655, 31082886609, 0, 0] := by
  rw [show A10K2.u7431 = KTree.node A10K2.t7438 (nat_lit 122272087) (nat_lit 5493653933) (nat_lit 0) A10K2.t7439 from rfl, totK_node, tot7438, tot7439]
  decide +kernel

theorem arows7435 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7435 = true := by
  rw [show A10K2.u7435 = KTree.node A10K2.t7440 (nat_lit 122278226) (nat_lit 12889788858) (nat_lit 0) A10K2.t7441 from rfl, allE_node, rows7440, irow7435, rows7441]
  all_goals rfl

theorem atot7435 : totK PA10K2 A10K2.u7435 = [0, 0, 464618952313, 2489926381393, 3993340696313, 1929819173384, 245863934142, 6121173289, 0, 0] := by
  rw [show A10K2.u7435 = KTree.node A10K2.t7440 (nat_lit 122278226) (nat_lit 12889788858) (nat_lit 0) A10K2.t7441 from rfl, totK_node, tot7440, tot7441]
  decide +kernel

theorem arows7436 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7436 = true := by
  rw [show A10K2.u7436 = KTree.node A10K2.t7442 (nat_lit 122285449) (nat_lit 8289344706) (nat_lit 0) A10K2.t7443 from rfl, allE_node, rows7442, irow7436, rows7443]
  all_goals rfl

theorem atot7436 : totK PA10K2 A10K2.u7436 = [0, 251986720587, 1593219031154, 3551910344646, 3331452001286, 1097043327654, 82980606153, 0, 0, 0] := by
  rw [show A10K2.u7436 = KTree.node A10K2.t7442 (nat_lit 122285449) (nat_lit 8289344706) (nat_lit 0) A10K2.t7443 from rfl, totK_node, tot7442, tot7443]
  decide +kernel

theorem arows7438 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7438 = true := by
  rw [show A10K2.u7438 = KTree.node A10K2.t7444 (nat_lit 122300316) (nat_lit 8864228820) (nat_lit 0) A10K2.t7445 from rfl, allE_node, rows7444, irow7438, rows7445]
  all_goals rfl

theorem atot7438 : totK PA10K2 A10K2.u7438 = [0, 798036173818, 3100600826093, 3899863489152, 1688469997694, 204228237195, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u7438 = KTree.node A10K2.t7444 (nat_lit 122300316) (nat_lit 8864228820) (nat_lit 0) A10K2.t7445 from rfl, totK_node, tot7444, tot7445]
  decide +kernel

theorem arows7439 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7439 = true := by
  rw [show A10K2.u7439 = KTree.node A10K2.t7446 (nat_lit 122305181) (nat_lit 5830957283) (nat_lit 0) A10K2.t7447 from rfl, allE_node, rows7446, irow7439, rows7447]
  all_goals rfl

theorem atot7439 : totK PA10K2 A10K2.u7439 = [0, 399736478239, 1983822205093, 3728602909784, 2844210512253, 633782123821, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u7439 = KTree.node A10K2.t7446 (nat_lit 122305181) (nat_lit 5830957283) (nat_lit 0) A10K2.t7447 from rfl, totK_node, tot7446, tot7447]
  decide +kernel

theorem arows7442 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7442 = true := by
  rw [show A10K2.u7442 = KTree.node A10K2.t7448 (nat_lit 122310913) (nat_lit 10329861105) (nat_lit 0) A10K2.t7449 from rfl, allE_node, rows7448, irow7442, rows7449]
  all_goals rfl

theorem atot7442 : totK PA10K2 A10K2.u7442 = [0, 334417811759, 2322768389386, 4183382722811, 2203546008195, 302097573152, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u7442 = KTree.node A10K2.t7448 (nat_lit 122310913) (nat_lit 10329861105) (nat_lit 0) A10K2.t7449 from rfl, totK_node, tot7448, tot7449]
  decide +kernel

theorem arows7443 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7443 = true := by
  rw [show A10K2.u7443 = KTree.node A10K2.t7450 (nat_lit 122333032) (nat_lit 5352180346) (nat_lit 0) A10K2.t7451 from rfl, allE_node, rows7450, irow7443, rows7451]
  all_goals rfl

theorem atot7443 : totK PA10K2 A10K2.u7443 = [0, 0, 1011550467770, 3712030770337, 3925210082414, 1004165853204, 45698881016, 0, 0, 0] := by
  rw [show A10K2.u7443 = KTree.node A10K2.t7450 (nat_lit 122333032) (nat_lit 5352180346) (nat_lit 0) A10K2.t7451 from rfl, totK_node, tot7450, tot7451]
  decide +kernel

theorem arows7445 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7445 = true := by
  rw [show A10K2.u7445 = KTree.node A10K2.t7452 (nat_lit 122341524) (nat_lit 12820410605) (nat_lit 0) A10K2.t7453 from rfl, allE_node, rows7452, irow7445, rows7453]
  all_goals rfl

theorem atot7445 : totK PA10K2 A10K2.u7445 = [0, 0, 701216718389, 3272840734568, 4076678639607, 1218718761502, 75447512833, 0, 0, 0] := by
  rw [show A10K2.u7445 = KTree.node A10K2.t7452 (nat_lit 122341524) (nat_lit 12820410605) (nat_lit 0) A10K2.t7453 from rfl, totK_node, tot7452, tot7453]
  decide +kernel

theorem arows7446 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7446 = true := by
  rw [show A10K2.u7446 = KTree.node A10K2.t7454 (nat_lit 122359222) (nat_lit 17057514467) (nat_lit 0) A10K2.t7455 from rfl, allE_node, rows7454, irow7446, rows7455]
  all_goals rfl

theorem atot7446 : totK PA10K2 A10K2.u7446 = [0, 511028321977, 2348411990386, 3646416634220, 2500222495241, 970712763605, 165558692469, 6354482628, 0, 0] := by
  rw [show A10K2.u7446 = KTree.node A10K2.t7454 (nat_lit 122359222) (nat_lit 17057514467) (nat_lit 0) A10K2.t7455 from rfl, totK_node, tot7454, tot7455]
  decide +kernel

theorem arows7451 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7451 = true := by
  rw [show A10K2.u7451 = KTree.node A10K2.t7456 (nat_lit 122366725) (nat_lit 6846869168) (nat_lit 0) A10K2.t7457 from rfl, allE_node, rows7456, irow7451, rows7457]
  all_goals rfl

theorem atot7451 : totK PA10K2 A10K2.u7451 = [0, 813214446787, 3295733350340, 4100279423726, 1627576055127, 149780495477, 0, 0, 0, 0] := by
  rw [show A10K2.u7451 = KTree.node A10K2.t7456 (nat_lit 122366725) (nat_lit 6846869168) (nat_lit 0) A10K2.t7457 from rfl, totK_node, tot7456, tot7457]
  decide +kernel

theorem arows7452 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7452 = true := by
  rw [show A10K2.u7452 = KTree.node A10K2.t7458 (nat_lit 122371520) (nat_lit 13544183307) (nat_lit 0) A10K2.t7459 from rfl, allE_node, rows7458, irow7452, rows7459]
  all_goals rfl

theorem atot7452 : totK PA10K2 A10K2.u7452 = [0, 522487195786, 2354808704163, 3892518138106, 2606702318452, 572317137180, 31747192500, 0, 0, 0] := by
  rw [show A10K2.u7452 = KTree.node A10K2.t7458 (nat_lit 122371520) (nat_lit 13544183307) (nat_lit 0) A10K2.t7459 from rfl, totK_node, tot7458, tot7459]
  decide +kernel

theorem arows7454 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7454 = true := by
  rw [show A10K2.u7454 = KTree.node A10K2.t7460 (nat_lit 122384836) (nat_lit 6366914825) (nat_lit 0) A10K2.t7461 from rfl, allE_node, rows7460, irow7454, rows7461]
  all_goals rfl

theorem atot7454 : totK PA10K2 A10K2.u7454 = [0, 323706995196, 2100106350323, 4195373070868, 2908998847410, 534926558706, 13816090359, 0, 0, 0] := by
  rw [show A10K2.u7454 = KTree.node A10K2.t7460 (nat_lit 122384836) (nat_lit 6366914825) (nat_lit 0) A10K2.t7461 from rfl, totK_node, tot7460, tot7461]
  decide +kernel

theorem arows7455 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7455 = true := by
  rw [show A10K2.u7455 = KTree.node A10K2.t7462 (nat_lit 122391771) (nat_lit 8588671786) (nat_lit 0) A10K2.t7463 from rfl, allE_node, rows7462, irow7455, rows7463]
  all_goals rfl

theorem atot7455 : totK PA10K2 A10K2.u7455 = [0, 0, 555853096202, 2805630336932, 4407337313171, 2243609742356, 294631720992, 6904928264, 0, 0] := by
  rw [show A10K2.u7455 = KTree.node A10K2.t7462 (nat_lit 122391771) (nat_lit 8588671786) (nat_lit 0) A10K2.t7463 from rfl, totK_node, tot7462, tot7463]
  decide +kernel

theorem arows7458 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7458 = true := by
  rw [show A10K2.u7458 = KTree.node A10K2.t7464 (nat_lit 122399085) (nat_lit 6390834543) (nat_lit 0) A10K2.t7465 from rfl, allE_node, rows7464, irow7458, rows7465]
  all_goals rfl

theorem atot7458 : totK PA10K2 A10K2.u7458 = [0, 0, 813070507670, 3293352896289, 4058539063751, 1607867340984, 147696859133, 0, 0, 0] := by
  rw [show A10K2.u7458 = KTree.node A10K2.t7464 (nat_lit 122399085) (nat_lit 6390834543) (nat_lit 0) A10K2.t7465 from rfl, totK_node, tot7464, tot7465]
  decide +kernel

theorem arows7459 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7459 = true := by
  rw [show A10K2.u7459 = KTree.node A10K2.t7466 (nat_lit 122413446) (nat_lit 15746881228) (nat_lit 0) A10K2.t7467 from rfl, allE_node, rows7466, irow7459, rows7467]
  all_goals rfl

theorem atot7459 : totK PA10K2 A10K2.u7459 = [0, 0, 671936312266, 2851096722050, 4073291662614, 2083004411749, 286109498653, 7047025452, 0, 0] := by
  rw [show A10K2.u7459 = KTree.node A10K2.t7466 (nat_lit 122413446) (nat_lit 15746881228) (nat_lit 0) A10K2.t7467 from rfl, totK_node, tot7466, tot7467]
  decide +kernel

theorem arows7461 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7461 = true := by
  rw [show A10K2.u7461 = KTree.node A10K2.t7468 (nat_lit 122418110) (nat_lit 16128367311) (nat_lit 0) A10K2.t7469 from rfl, allE_node, rows7468, irow7461, rows7469]
  all_goals rfl

theorem atot7461 : totK PA10K2 A10K2.u7461 = [0, 0, 173547141522, 1688021500619, 4146555105967, 3285026265606, 638521732361, 17977415720, 0, 0] := by
  rw [show A10K2.u7461 = KTree.node A10K2.t7468 (nat_lit 122418110) (nat_lit 16128367311) (nat_lit 0) A10K2.t7469 from rfl, totK_node, tot7468, tot7469]
  decide +kernel

theorem arows7462 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7462 = true := by
  rw [show A10K2.u7462 = KTree.node A10K2.t7470 (nat_lit 122497258) (nat_lit 12436460845) (nat_lit 0) A10K2.t7471 from rfl, allE_node, rows7470, irow7462, rows7471]
  all_goals rfl

theorem atot7462 : totK PA10K2 A10K2.u7462 = [0, 0, 869750410530, 3262164018238, 3695066405658, 1543068188476, 402102147866, 43132710386, 0, 0] := by
  rw [show A10K2.u7462 = KTree.node A10K2.t7470 (nat_lit 122497258) (nat_lit 12436460845) (nat_lit 0) A10K2.t7471 from rfl, totK_node, tot7470, tot7471]
  decide +kernel

theorem arows7466 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7466 = true := by
  rw [show A10K2.u7466 = KTree.node A10K2.t7472 (nat_lit 122501909) (nat_lit 7002275741) (nat_lit 0) A10K2.t7473 from rfl, allE_node, rows7472, irow7466, rows7473]
  all_goals rfl

theorem atot7466 : totK PA10K2 A10K2.u7466 = [0, 0, 411997530451, 2040834614909, 3717123061682, 2692004404234, 585039604832, 31768748853, 0, 0] := by
  rw [show A10K2.u7466 = KTree.node A10K2.t7472 (nat_lit 122501909) (nat_lit 7002275741) (nat_lit 0) A10K2.t7473 from rfl, totK_node, tot7472, tot7473]
  decide +kernel

theorem arows7467 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7467 = true := by
  rw [show A10K2.u7467 = KTree.node A10K2.t7474 (nat_lit 122508474) (nat_lit 14904189911) (nat_lit 0) A10K2.t7475 from rfl, allE_node, rows7474, irow7467, rows7475]
  all_goals rfl

theorem atot7467 : totK PA10K2 A10K2.u7467 = [0, 0, 448372694464, 2464967751661, 4057946546713, 1984830082983, 247202306788, 6239673734, 0, 0] := by
  rw [show A10K2.u7467 = KTree.node A10K2.t7474 (nat_lit 122508474) (nat_lit 14904189911) (nat_lit 0) A10K2.t7475 from rfl, totK_node, tot7474, tot7475]
  decide +kernel

theorem arows7469 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7469 = true := by
  rw [show A10K2.u7469 = KTree.node A10K2.t7476 (nat_lit 122514903) (nat_lit 14430147840) (nat_lit 0) A10K2.t7477 from rfl, allE_node, rows7476, irow7469, rows7477]
  all_goals rfl

theorem atot7469 : totK PA10K2 A10K2.u7469 = [0, 0, 609977757965, 2824551982846, 4306195087617, 2195859790599, 251760260885, 0, 0, 0] := by
  rw [show A10K2.u7469 = KTree.node A10K2.t7476 (nat_lit 122514903) (nat_lit 14430147840) (nat_lit 0) A10K2.t7477 from rfl, totK_node, tot7476, tot7477]
  decide +kernel

theorem arows7470 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7470 = true := by
  rw [show A10K2.u7470 = KTree.node A10K2.t7478 (nat_lit 122529058) (nat_lit 13708722487) (nat_lit 0) A10K2.t7479 from rfl, allE_node, rows7478, irow7470, rows7479]
  all_goals rfl

theorem atot7470 : totK PA10K2 A10K2.u7470 = [0, 0, 0, 944430262108, 3532780748040, 3907447641199, 1173325641100, 73586045739, 0, 0] := by
  rw [show A10K2.u7470 = KTree.node A10K2.t7478 (nat_lit 122529058) (nat_lit 13708722487) (nat_lit 0) A10K2.t7479 from rfl, totK_node, tot7478, tot7479]
  decide +kernel

theorem arows7473 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7473 = true := by
  rw [show A10K2.u7473 = KTree.node A10K2.t7480 (nat_lit 122533652) (nat_lit 12421074374) (nat_lit 0) A10K2.t7481 from rfl, allE_node, rows7480, irow7473, rows7481]
  all_goals rfl

theorem atot7473 : totK PA10K2 A10K2.u7473 = [0, 0, 0, 339672587719, 2057270210309, 3827937685751, 2591506361935, 555191225044, 31018567651, 0] := by
  rw [show A10K2.u7473 = KTree.node A10K2.t7480 (nat_lit 122533652) (nat_lit 12421074374) (nat_lit 0) A10K2.t7481 from rfl, totK_node, tot7480, tot7481]
  decide +kernel

theorem arows7474 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7474 = true := by
  rw [show A10K2.u7474 = KTree.node A10K2.t7482 (nat_lit 122538308) (nat_lit 13109807505) (nat_lit 0) A10K2.t7483 from rfl, allE_node, rows7482, irow7474, rows7483]
  all_goals rfl

theorem atot7474 : totK PA10K2 A10K2.u7474 = [0, 0, 0, 559501797500, 2816572191580, 4100846018298, 1483618825764, 109738100044, 0, 0] := by
  rw [show A10K2.u7474 = KTree.node A10K2.t7482 (nat_lit 122538308) (nat_lit 13109807505) (nat_lit 0) A10K2.t7483 from rfl, totK_node, tot7482, tot7483]
  decide +kernel

theorem arows7476 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7476 = true := by
  rw [show A10K2.u7476 = KTree.node A10K2.t7484 (nat_lit 122547356) (nat_lit 9751260768) (nat_lit 0) A10K2.t7485 from rfl, allE_node, rows7484, irow7476, rows7485]
  all_goals rfl

theorem atot7476 : totK PA10K2 A10K2.u7476 = [0, 0, 251986720587, 1732136404863, 3526417552530, 2969655547053, 1137515878294, 173570996746, 5685526223, 0] := by
  rw [show A10K2.u7476 = KTree.node A10K2.t7484 (nat_lit 122547356) (nat_lit 9751260768) (nat_lit 0) A10K2.t7485 from rfl, totK_node, tot7484, tot7485]
  decide +kernel

theorem arows7477 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7477 = true := by
  rw [show A10K2.u7477 = KTree.node A10K2.t7486 (nat_lit 122562438) (nat_lit 14028018008) (nat_lit 0) A10K2.t7487 from rfl, allE_node, rows7486, irow7477, rows7487]
  all_goals rfl

theorem atot7477 : totK PA10K2 A10K2.u7477 = [0, 0, 798036173818, 3131180160072, 3961419374675, 1612262348138, 156559184042, 5460492893, 0, 0] := by
  rw [show A10K2.u7477 = KTree.node A10K2.t7486 (nat_lit 122562438) (nat_lit 14028018008) (nat_lit 0) A10K2.t7487 from rfl, totK_node, tot7486, tot7487]
  decide +kernel

theorem arows7483 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7483 = true := by
  rw [show A10K2.u7483 = KTree.node A10K2.t7488 (nat_lit 122567319) (nat_lit 11036217250) (nat_lit 0) A10K2.t7489 from rfl, allE_node, rows7488, irow7483, rows7489]
  all_goals rfl

theorem atot7483 : totK PA10K2 A10K2.u7483 = [0, 0, 452811472891, 2107148803572, 3711276557024, 2730518207178, 603347992048, 31768748853, 0, 0] := by
  rw [show A10K2.u7483 = KTree.node A10K2.t7488 (nat_lit 122567319) (nat_lit 11036217250) (nat_lit 0) A10K2.t7489 from rfl, totK_node, tot7488, tot7489]
  decide +kernel

theorem arows7484 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7484 = true := by
  rw [show A10K2.u7484 = KTree.node A10K2.t7490 (nat_lit 122573098) (nat_lit 10679259678) (nat_lit 0) A10K2.t7491 from rfl, allE_node, rows7490, irow7484, rows7491]
  all_goals rfl

theorem atot7484 : totK PA10K2 A10K2.u7484 = [0, 0, 290643499251, 2225108048915, 4252351157983, 2230181997764, 262267536880, 6354482628, 0, 0] := by
  rw [show A10K2.u7484 = KTree.node A10K2.t7490 (nat_lit 122573098) (nat_lit 10679259678) (nat_lit 0) A10K2.t7491 from rfl, totK_node, tot7490, tot7491]
  decide +kernel

theorem arows7486 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7486 = true := by
  rw [show A10K2.u7486 = KTree.node A10K2.t7492 (nat_lit 122595340) (nat_lit 11630346924) (nat_lit 0) A10K2.t7493 from rfl, allE_node, rows7492, irow7486, rows7493]
  all_goals rfl

theorem atot7486 : totK PA10K2 A10K2.u7486 = [0, 0, 0, 1032162819688, 3780177175032, 3831239292022, 906051001194, 45352262510, 0, 0] := by
  rw [show A10K2.u7486 = KTree.node A10K2.t7492 (nat_lit 122595340) (nat_lit 11630346924) (nat_lit 0) A10K2.t7493 from rfl, totK_node, tot7492, tot7493]
  decide +kernel

theorem arows7487 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7487 = true := by
  rw [show A10K2.u7487 = KTree.node A10K2.t7494 (nat_lit 122603757) (nat_lit 5988600851) (nat_lit 0) A10K2.t7495 from rfl, allE_node, rows7494, irow7487, rows7495]
  all_goals rfl

theorem atot7487 : totK PA10K2 A10K2.u7487 = [0, 0, 0, 632567318816, 3118352436494, 4096655221762, 1294821175133, 95264255974, 0, 0] := by
  rw [show A10K2.u7487 = KTree.node A10K2.t7494 (nat_lit 122603757) (nat_lit 5988600851) (nat_lit 0) A10K2.t7495 from rfl, totK_node, tot7494, tot7495]
  decide +kernel

theorem arows7490 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7490 = true := by
  rw [show A10K2.u7490 = KTree.node A10K2.t7496 (nat_lit 122621453) (nat_lit 4432005353) (nat_lit 0) A10K2.t7497 from rfl, allE_node, rows7496, irow7490, rows7497]
  all_goals rfl

theorem atot7490 : totK PA10K2 A10K2.u7490 = [0, 0, 553966405266, 2437971007701, 3774322266736, 2478471962334, 822498691587, 138218344971, 6239673734, 0] := by
  rw [show A10K2.u7490 = KTree.node A10K2.t7496 (nat_lit 122621453) (nat_lit 4432005353) (nat_lit 0) A10K2.t7497 from rfl, totK_node, tot7496, tot7497]
  decide +kernel

theorem arows7491 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7491 = true := by
  rw [show A10K2.u7491 = KTree.node A10K2.t7498 (nat_lit 122629168) (nat_lit 13919293850) (nat_lit 0) A10K2.t7499 from rfl, allE_node, rows7498, irow7491, rows7499]
  all_goals rfl

theorem atot7491 : totK PA10K2 A10K2.u7491 = [0, 0, 767173304411, 3232263845673, 4131435656473, 1660450088372, 153784458101, 0, 0, 0] := by
  rw [show A10K2.u7491 = KTree.node A10K2.t7498 (nat_lit 122629168) (nat_lit 13919293850) (nat_lit 0) A10K2.t7499 from rfl, totK_node, tot7498, tot7499]
  decide +kernel

theorem arows7493 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7493 = true := by
  rw [show A10K2.u7493 = KTree.node A10K2.t7500 (nat_lit 122642490) (nat_lit 10398107740) (nat_lit 0) A10K2.t7501 from rfl, allE_node, rows7500, irow7493, rows7501]
  all_goals rfl

theorem atot7493 : totK PA10K2 A10K2.u7493 = [0, 0, 574144885511, 2506155007472, 3860749192955, 2395140124307, 527369964561, 31285368086, 0, 0] := by
  rw [show A10K2.u7493 = KTree.node A10K2.t7500 (nat_lit 122642490) (nat_lit 10398107740) (nat_lit 0) A10K2.t7501 from rfl, totK_node, tot7500, tot7501]
  decide +kernel

theorem arows7494 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7494 = true := by
  rw [show A10K2.u7494 = KTree.node A10K2.t7502 (nat_lit 122647108) (nat_lit 8228796389) (nat_lit 0) A10K2.t7503 from rfl, allE_node, rows7502, irow7494, rows7503]
  all_goals rfl

theorem atot7494 : totK PA10K2 A10K2.u7494 = [0, 0, 271126488874, 1945781940912, 4216438735790, 3088565136626, 563312925215, 13244237517, 0, 0] := by
  rw [show A10K2.u7494 = KTree.node A10K2.t7502 (nat_lit 122647108) (nat_lit 8228796389) (nat_lit 0) A10K2.t7503 from rfl, totK_node, tot7502, tot7503]
  decide +kernel

theorem arows7498 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7498 = true := by
  rw [show A10K2.u7498 = KTree.node A10K2.t7504 (nat_lit 122759232) (nat_lit 9106998413) (nat_lit 0) A10K2.t7505 from rfl, allE_node, rows7504, irow7498, rows7505]
  all_goals rfl

theorem atot7498 : totK PA10K2 A10K2.u7498 = [0, 842026830166, 3083849721715, 3297563167185, 1224747571119, 814866276627, 458303640743, 49137922124, 0, 0] := by
  rw [show A10K2.u7498 = KTree.node A10K2.t7504 (nat_lit 122759232) (nat_lit 9106998413) (nat_lit 0) A10K2.t7505 from rfl, totK_node, tot7504, tot7505]
  decide +kernel

theorem arows7499 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7499 = true := by
  rw [show A10K2.u7499 = KTree.node A10K2.t7506 (nat_lit 122763923) (nat_lit 10899815526) (nat_lit 0) A10K2.t7507 from rfl, allE_node, rows7506, irow7499, rows7507]
  all_goals rfl

theorem atot7499 : totK PA10K2 A10K2.u7499 = [0, 347345712664, 1847008625105, 3767412090623, 2935736852182, 639054508700, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u7499 = KTree.node A10K2.t7506 (nat_lit 122763923) (nat_lit 10899815526) (nat_lit 0) A10K2.t7507 from rfl, totK_node, tot7506, tot7507]
  decide +kernel

theorem arows7501 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7501 = true := by
  rw [show A10K2.u7501 = KTree.node A10K2.t7508 (nat_lit 122769417) (nat_lit 9797965543) (nat_lit 0) A10K2.t7509 from rfl, allE_node, rows7508, irow7501, rows7509]
  all_goals rfl

theorem atot7501 : totK PA10K2 A10K2.u7501 = [0, 403451872644, 2454073548009, 4212510457291, 2149097531336, 232248588597, 0, 0, 0, 0] := by
  rw [show A10K2.u7501 = KTree.node A10K2.t7508 (nat_lit 122769417) (nat_lit 9797965543) (nat_lit 0) A10K2.t7509 from rfl, totK_node, tot7508, tot7509]
  decide +kernel

theorem arows7502 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7502 = true := by
  rw [show A10K2.u7502 = KTree.node A10K2.t7510 (nat_lit 122777200) (nat_lit 13396495340) (nat_lit 0) A10K2.t7511 from rfl, allE_node, rows7510, irow7502, rows7511]
  all_goals rfl

theorem atot7502 : totK PA10K2 A10K2.u7502 = [0, 595155796918, 2724492739973, 4152519068997, 2329918839852, 401041916327, 13317224979, 0, 0, 0] := by
  rw [show A10K2.u7502 = KTree.node A10K2.t7510 (nat_lit 122777200) (nat_lit 13396495340) (nat_lit 0) A10K2.t7511 from rfl, totK_node, tot7510, tot7511]
  decide +kernel

theorem arows7505 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7505 = true := by
  rw [show A10K2.u7505 = KTree.node A10K2.t7512 (nat_lit 122791827) (nat_lit 10671537095) (nat_lit 0) A10K2.t7513 from rfl, allE_node, rows7512, irow7505, rows7513]
  all_goals rfl

theorem atot7505 : totK PA10K2 A10K2.u7505 = [0, 0, 883921920065, 3532081202182, 4041597503375, 1262442114405, 75296538425, 0, 0, 0] := by
  rw [show A10K2.u7505 = KTree.node A10K2.t7512 (nat_lit 122791827) (nat_lit 10671537095) (nat_lit 0) A10K2.t7513 from rfl, totK_node, tot7512, tot7513]
  decide +kernel

theorem arows7506 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7506 = true := by
  rw [show A10K2.u7506 = KTree.node A10K2.t7514 (nat_lit 122796544) (nat_lit 9183273032) (nat_lit 0) A10K2.t7515 from rfl, allE_node, rows7514, irow7506, rows7515]
  all_goals rfl

theorem atot7506 : totK PA10K2 A10K2.u7506 = [0, 0, 385160669654, 2069821895954, 3816520519920, 2615181139558, 566268925200, 31082886609, 0, 0] := by
  rw [show A10K2.u7506 = KTree.node A10K2.t7514 (nat_lit 122796544) (nat_lit 9183273032) (nat_lit 0) A10K2.t7515 from rfl, totK_node, tot7514, tot7515]
  decide +kernel

theorem arows7508 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7508 = true := by
  rw [show A10K2.u7508 = KTree.node A10K2.t7516 (nat_lit 122802452) (nat_lit 13104907840) (nat_lit 0) A10K2.t7517 from rfl, allE_node, rows7516, irow7508, rows7517]
  all_goals rfl

theorem atot7508 : totK PA10K2 A10K2.u7508 = [0, 0, 479099007309, 2548066326416, 4172929652616, 1949658965305, 228655978291, 6121173289, 0, 0] := by
  rw [show A10K2.u7508 = KTree.node A10K2.t7516 (nat_lit 122802452) (nat_lit 13104907840) (nat_lit 0) A10K2.t7517 from rfl, totK_node, tot7516, tot7517]
  decide +kernel

theorem arows7509 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7509 = true := by
  rw [show A10K2.u7509 = KTree.node A10K2.t7518 (nat_lit 122810266) (nat_lit 14464902404) (nat_lit 0) A10K2.t7519 from rfl, allE_node, rows7518, irow7509, rows7519]
  all_goals rfl

theorem atot7509 : totK PA10K2 A10K2.u7509 = [0, 561156172308, 2292670431147, 3518449313167, 2685113520882, 868228613362, 62908894840, 0, 0, 0] := by
  rw [show A10K2.u7509 = KTree.node A10K2.t7518 (nat_lit 122810266) (nat_lit 14464902404) (nat_lit 0) A10K2.t7519 from rfl, totK_node, tot7518, tot7519]
  decide +kernel

theorem arows7514 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7514 = true := by
  rw [show A10K2.u7514 = KTree.node A10K2.t7520 (nat_lit 122820935) (nat_lit 5381572638) (nat_lit 0) A10K2.t7521 from rfl, allE_node, rows7520, irow7514, rows7521]
  all_goals rfl

theorem atot7514 : totK PA10K2 A10K2.u7514 = [0, 472607646069, 2237275521482, 3839616599956, 2409772302205, 471384151039, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u7514 = KTree.node A10K2.t7520 (nat_lit 122820935) (nat_lit 5381572638) (nat_lit 0) A10K2.t7521 from rfl, totK_node, tot7520, tot7521]
  decide +kernel

theorem arows7515 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7515 = true := by
  rw [show A10K2.u7515 = KTree.node A10K2.t7522 (nat_lit 122828130) (nat_lit 13046092967) (nat_lit 0) A10K2.t7523 from rfl, allE_node, rows7522, irow7515, rows7523]
  all_goals rfl

theorem atot7515 : totK PA10K2 A10K2.u7515 = [0, 294540382597, 2031942444742, 3992928134038, 2747314230751, 581704854090, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u7515 = KTree.node A10K2.t7522 (nat_lit 122828130) (nat_lit 13046092967) (nat_lit 0) A10K2.t7523 from rfl, totK_node, tot7522, tot7523]
  decide +kernel

theorem arows7517 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7517 = true := by
  rw [show A10K2.u7517 = KTree.node A10K2.t7524 (nat_lit 122832568) (nat_lit 3826789625) (nat_lit 0) A10K2.t7525 from rfl, allE_node, rows7524, irow7517, rows7525]
  all_goals rfl

theorem atot7517 : totK PA10K2 A10K2.u7517 = [0, 820824437048, 3267884261001, 3917747046019, 1390229478008, 115141541143, 0, 0, 0, 0] := by
  rw [show A10K2.u7517 = KTree.node A10K2.t7524 (nat_lit 122832568) (nat_lit 3826789625) (nat_lit 0) A10K2.t7525 from rfl, totK_node, tot7524, tot7525]
  decide +kernel

theorem arows7518 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7518 = true := by
  rw [show A10K2.u7518 = KTree.node A10K2.t7526 (nat_lit 122847310) (nat_lit 10856236912) (nat_lit 0) A10K2.t7527 from rfl, allE_node, rows7526, irow7518, rows7527]
  all_goals rfl

theorem atot7518 : totK PA10K2 A10K2.u7518 = [0, 0, 1187500296280, 3945924759323, 3529498805776, 769542853169, 38342359577, 0, 0, 0] := by
  rw [show A10K2.u7518 = KTree.node A10K2.t7526 (nat_lit 122847310) (nat_lit 10856236912) (nat_lit 0) A10K2.t7527 from rfl, totK_node, tot7526, tot7527]
  decide +kernel

theorem arows7521 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7521 = true := by
  rw [show A10K2.u7521 = KTree.node A10K2.t7528 (nat_lit 122858146) (nat_lit 14114488693) (nat_lit 0) A10K2.t7529 from rfl, allE_node, rows7528, irow7521, rows7529]
  all_goals rfl

theorem atot7521 : totK PA10K2 A10K2.u7521 = [0, 0, 976696988614, 3635662995387, 3832197367640, 1065200034470, 64078106957, 0, 0, 0] := by
  rw [show A10K2.u7521 = KTree.node A10K2.t7528 (nat_lit 122858146) (nat_lit 14114488693) (nat_lit 0) A10K2.t7529 from rfl, totK_node, tot7528, tot7529]
  decide +kernel

theorem arows7522 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7522 = true := by
  rw [show A10K2.u7522 = KTree.node A10K2.t7530 (nat_lit 122866338) (nat_lit 13905161396) (nat_lit 0) A10K2.t7531 from rfl, allE_node, rows7530, irow7522, rows7531]
  all_goals rfl

theorem atot7522 : totK PA10K2 A10K2.u7522 = [0, 0, 577583254698, 2900027347196, 4190528425826, 1563621652040, 143897169859, 0, 0, 0] := by
  rw [show A10K2.u7522 = KTree.node A10K2.t7530 (nat_lit 122866338) (nat_lit 13905161396) (nat_lit 0) A10K2.t7531 from rfl, totK_node, tot7530, tot7531]
  decide +kernel

theorem arows7524 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7524 = true := by
  rw [show A10K2.u7524 = KTree.node A10K2.t7532 (nat_lit 123021544) (nat_lit 6730958280) (nat_lit 0) A10K2.t7533 from rfl, allE_node, rows7532, irow7524, rows7533]
  all_goals rfl

theorem atot7524 : totK PA10K2 A10K2.u7524 = [0, 0, 842026830166, 3196383948617, 3820401852493, 1587537433509, 231326313981, 6354482628, 0, 0] := by
  rw [show A10K2.u7524 = KTree.node A10K2.t7532 (nat_lit 123021544) (nat_lit 6730958280) (nat_lit 0) A10K2.t7533 from rfl, totK_node, tot7532, tot7533]
  decide +kernel

theorem arows7525 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7525 = true := by
  rw [show A10K2.u7525 = KTree.node A10K2.t7534 (nat_lit 123026276) (nat_lit 13625692995) (nat_lit 0) A10K2.t7535 from rfl, allE_node, rows7534, irow7525, rows7535]
  all_goals rfl

theorem atot7525 : totK PA10K2 A10K2.u7525 = [0, 0, 461452330429, 2203797656052, 3728538357327, 2551145253706, 546219774629, 31452573850, 0, 0] := by
  rw [show A10K2.u7525 = KTree.node A10K2.t7534 (nat_lit 123026276) (nat_lit 13625692995) (nat_lit 0) A10K2.t7535 from rfl, totK_node, tot7534, tot7535]
  decide +kernel

theorem arows7529 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7529 = true := by
  rw [show A10K2.u7529 = KTree.node A10K2.t7536 (nat_lit 123032753) (nat_lit 1745519145) (nat_lit 0) A10K2.t7537 from rfl, allE_node, rows7536, irow7529, rows7537]
  all_goals rfl

theorem atot7529 : totK PA10K2 A10K2.u7529 = [0, 0, 488863735739, 2494354784706, 4078234005211, 2074457387064, 251126255590, 6354482628, 0, 0] := by
  rw [show A10K2.u7529 = KTree.node A10K2.t7536 (nat_lit 123032753) (nat_lit 1745519145) (nat_lit 0) A10K2.t7537 from rfl, totK_node, tot7536, tot7537]
  decide +kernel

theorem arows7530 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7530 = true := by
  rw [show A10K2.u7530 = KTree.node A10K2.t7538 (nat_lit 123039739) (nat_lit 6018884933) (nat_lit 0) A10K2.t7539 from rfl, allE_node, rows7538, irow7530, rows7539]
  all_goals rfl

theorem atot7530 : totK PA10K2 A10K2.u7530 = [0, 0, 552389142829, 2646007593163, 4264225556605, 2384234769330, 335866575750, 6962742351, 0, 0] := by
  rw [show A10K2.u7530 = KTree.node A10K2.t7538 (nat_lit 123039739) (nat_lit 6018884933) (nat_lit 0) A10K2.t7539 from rfl, totK_node, tot7538, tot7539]
  decide +kernel

theorem arows7532 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7532 = true := by
  rw [show A10K2.u7532 = KTree.node A10K2.t7540 (nat_lit 123080769) (nat_lit 10405391659) (nat_lit 0) A10K2.t7541 from rfl, allE_node, rows7540, irow7532, rows7541]
  all_goals rfl

theorem atot7532 : totK PA10K2 A10K2.u7532 = [0, 0, 687788130228, 2904393246986, 3954409856157, 1741158910742, 220223625965, 5460492893, 0, 0] := by
  rw [show A10K2.u7532 = KTree.node A10K2.t7540 (nat_lit 123080769) (nat_lit 10405391659) (nat_lit 0) A10K2.t7541 from rfl, totK_node, tot7540, tot7541]
  decide +kernel

theorem arows7533 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7533 = true := by
  rw [show A10K2.u7533 = KTree.node A10K2.t7542 (nat_lit 123088284) (nat_lit 8144844210) (nat_lit 0) A10K2.t7543 from rfl, allE_node, rows7542, irow7533, rows7543]
  all_goals rfl

theorem atot7533 : totK PA10K2 A10K2.u7533 = [0, 0, 467313866300, 2571363374889, 4119296596745, 2066119585647, 344631200639, 24969229125, 0, 0] := by
  rw [show A10K2.u7533 = KTree.node A10K2.t7542 (nat_lit 123088284) (nat_lit 8144844210) (nat_lit 0) A10K2.t7543 from rfl, totK_node, tot7542, tot7543]
  decide +kernel

theorem arows7536 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7536 = true := by
  rw [show A10K2.u7536 = KTree.node A10K2.t7544 (nat_lit 123093857) (nat_lit 8989251321) (nat_lit 0) A10K2.t7545 from rfl, allE_node, rows7544, irow7536, rows7545]
  all_goals rfl

theorem atot7536 : totK PA10K2 A10K2.u7536 = [0, 0, 819213633141, 3036787063644, 3696332160805, 1646053527530, 228161098472, 6034215561, 0, 0] := by
  rw [show A10K2.u7536 = KTree.node A10K2.t7544 (nat_lit 123093857) (nat_lit 8989251321) (nat_lit 0) A10K2.t7545 from rfl, totK_node, tot7544, tot7545]
  decide +kernel

theorem arows7537 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7537 = true := by
  rw [show A10K2.u7537 = KTree.node A10K2.t7546 (nat_lit 123099410) (nat_lit 14212334152) (nat_lit 0) A10K2.t7547 from rfl, allE_node, rows7546, irow7537, rows7547]
  all_goals rfl

theorem atot7537 : totK PA10K2 A10K2.u7537 = [0, 0, 0, 1475519401603, 4351217004470, 3006648691044, 479067036306, 11740475125, 0, 0] := by
  rw [show A10K2.u7537 = KTree.node A10K2.t7546 (nat_lit 123099410) (nat_lit 14212334152) (nat_lit 0) A10K2.t7547 from rfl, totK_node, tot7546, tot7547]
  decide +kernel

theorem arows7539 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7539 = true := by
  rw [show A10K2.u7539 = KTree.node A10K2.t7548 (nat_lit 123119767) (nat_lit 11586267033) (nat_lit 0) A10K2.t7549 from rfl, allE_node, rows7548, irow7539, rows7549]
  all_goals rfl

theorem atot7539 : totK PA10K2 A10K2.u7539 = [0, 0, 0, 1094771518193, 3933458355574, 3602408768768, 727928134396, 38045387652, 0, 0] := by
  rw [show A10K2.u7539 = KTree.node A10K2.t7548 (nat_lit 123119767) (nat_lit 11586267033) (nat_lit 0) A10K2.t7549 from rfl, totK_node, tot7548, tot7549]
  decide +kernel

theorem arows7540 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7540 = true := by
  rw [show A10K2.u7540 = KTree.node A10K2.t7550 (nat_lit 123128368) (nat_lit 13299525371) (nat_lit 0) A10K2.t7551 from rfl, allE_node, rows7550, irow7540, rows7551]
  all_goals rfl

theorem atot7540 : totK PA10K2 A10K2.u7540 = [0, 0, 0, 570545335347, 2868101437596, 4102681664102, 1477787983407, 112922155649, 0, 0] := by
  rw [show A10K2.u7540 = KTree.node A10K2.t7550 (nat_lit 123128368) (nat_lit 13299525371) (nat_lit 0) A10K2.t7551 from rfl, totK_node, tot7550, tot7551]
  decide +kernel

theorem arows7547 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7547 = true := by
  rw [show A10K2.u7547 = KTree.node A10K2.t7552 (nat_lit 123210252) (nat_lit 11679243042) (nat_lit 0) A10K2.t7553 from rfl, allE_node, rows7552, irow7547, rows7553]
  all_goals rfl

theorem atot7547 : totK PA10K2 A10K2.u7547 = [0, 776609848865, 3143143245915, 3774908731334, 1308267766796, 331152551877, 419902306845, 136682872893, 6354482628, 0] := by
  rw [show A10K2.u7547 = KTree.node A10K2.t7552 (nat_lit 123210252) (nat_lit 11679243042) (nat_lit 0) A10K2.t7553 from rfl, totK_node, tot7552, tot7553]
  decide +kernel

theorem arows7548 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7548 = true := by
  rw [show A10K2.u7548 = KTree.node A10K2.t7554 (nat_lit 123232352) (nat_lit 13865624482) (nat_lit 0) A10K2.t7555 from rfl, allE_node, rows7554, irow7548, rows7555]
  all_goals rfl

theorem atot7548 : totK PA10K2 A10K2.u7548 = [0, 633216403460, 2624069202134, 3993807391039, 2404422210080, 433274505575, 13364899180, 0, 0, 0] := by
  rw [show A10K2.u7548 = KTree.node A10K2.t7554 (nat_lit 123232352) (nat_lit 13865624482) (nat_lit 0) A10K2.t7555 from rfl, totK_node, tot7554, tot7555]
  decide +kernel

theorem arows7550 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7550 = true := by
  rw [show A10K2.u7550 = KTree.node A10K2.t7556 (nat_lit 123237132) (nat_lit 10351411981) (nat_lit 0) A10K2.t7557 from rfl, allE_node, rows7556, irow7550, rows7557]
  all_goals rfl

theorem atot7550 : totK PA10K2 A10K2.u7550 = [0, 177435414779, 1711131225168, 4153864424516, 3510942594772, 765508040247, 19707287507, 0, 0, 0] := by
  rw [show A10K2.u7550 = KTree.node A10K2.t7556 (nat_lit 123237132) (nat_lit 10351411981) (nat_lit 0) A10K2.t7557 from rfl, totK_node, tot7556, tot7557]
  decide +kernel

theorem arows7551 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7551 = true := by
  rw [show A10K2.u7551 = KTree.node A10K2.t7558 (nat_lit 123243052) (nat_lit 12570484968) (nat_lit 0) A10K2.t7559 from rfl, allE_node, rows7558, irow7551, rows7559]
  all_goals rfl

theorem atot7551 : totK PA10K2 A10K2.u7551 = [0, 0, 776122765669, 3249401753335, 4147800307416, 1604377484418, 156027899771, 0, 0, 0] := by
  rw [show A10K2.u7551 = KTree.node A10K2.t7558 (nat_lit 123243052) (nat_lit 12570484968) (nat_lit 0) A10K2.t7559 from rfl, totK_node, tot7558, tot7559]
  decide +kernel

theorem arows7554 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7554 = true := by
  rw [show A10K2.u7554 = KTree.node A10K2.t7560 (nat_lit 123265430) (nat_lit 15715677148) (nat_lit 0) A10K2.t7561 from rfl, allE_node, rows7560, irow7554, rows7561]
  all_goals rfl

theorem atot7554 : totK PA10K2 A10K2.u7554 = [0, 0, 825712571293, 3075833361134, 3855970097405, 1923811399916, 353807224773, 13364899180, 0, 0] := by
  rw [show A10K2.u7554 = KTree.node A10K2.t7560 (nat_lit 123265430) (nat_lit 15715677148) (nat_lit 0) A10K2.t7561 from rfl, totK_node, tot7560, tot7561]
  decide +kernel

theorem arows7555 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7555 = true := by
  rw [show A10K2.u7555 = KTree.node A10K2.t7562 (nat_lit 123283349) (nat_lit 5171259390) (nat_lit 0) A10K2.t7563 from rfl, allE_node, rows7562, irow7555, rows7563]
  all_goals rfl

theorem atot7555 : totK PA10K2 A10K2.u7555 = [0, 838891203471, 2976843997706, 3501781510237, 1913498102864, 577490465264, 50548650670, 0, 0, 0] := by
  rw [show A10K2.u7555 = KTree.node A10K2.t7562 (nat_lit 123283349) (nat_lit 5171259390) (nat_lit 0) A10K2.t7563 from rfl, totK_node, tot7562, tot7563]
  decide +kernel

theorem arows7557 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7557 = true := by
  rw [show A10K2.u7557 = KTree.node A10K2.t7564 (nat_lit 123287894) (nat_lit 10018042833) (nat_lit 0) A10K2.t7565 from rfl, allE_node, rows7564, irow7557, rows7565]
  all_goals rfl

theorem atot7557 : totK PA10K2 A10K2.u7557 = [0, 288866287467, 1848674871557, 3868471544965, 2955197194601, 635824030183, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u7557 = KTree.node A10K2.t7564 (nat_lit 123287894) (nat_lit 10018042833) (nat_lit 0) A10K2.t7565 from rfl, totK_node, tot7564, tot7565]
  decide +kernel

theorem arows7558 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7558 = true := by
  rw [show A10K2.u7558 = KTree.node A10K2.t7566 (nat_lit 123295935) (nat_lit 5767331198) (nat_lit 0) A10K2.t7567 from rfl, allE_node, rows7566, irow7558, rows7567]
  all_goals rfl

theorem atot7558 : totK PA10K2 A10K2.u7558 = [0, 735885384861, 2976022548564, 3962945285201, 1761154011143, 218493000883, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u7558 = KTree.node A10K2.t7566 (nat_lit 123295935) (nat_lit 5767331198) (nat_lit 0) A10K2.t7567 from rfl, totK_node, tot7566, tot7567]
  decide +kernel

theorem arows7562 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7562 = true := by
  rw [show A10K2.u7562 = KTree.node A10K2.t7568 (nat_lit 123301886) (nat_lit 15844512021) (nat_lit 0) A10K2.t7569 from rfl, allE_node, rows7568, irow7562, rows7569]
  all_goals rfl

theorem atot7562 : totK PA10K2 A10K2.u7562 = [0, 319364795913, 2144643355962, 4284912605578, 2911523472253, 543985667664, 13814447077, 0, 0, 0] := by
  rw [show A10K2.u7562 = KTree.node A10K2.t7568 (nat_lit 123301886) (nat_lit 15844512021) (nat_lit 0) A10K2.t7569 from rfl, totK_node, tot7568, tot7569]
  decide +kernel

theorem arows7563 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7563 = true := by
  rw [show A10K2.u7563 = KTree.node A10K2.t7570 (nat_lit 123315897) (nat_lit 2580542478) (nat_lit 0) A10K2.t7571 from rfl, allE_node, rows7570, irow7563, rows7571]
  all_goals rfl

theorem atot7563 : totK PA10K2 A10K2.u7563 = [0, 0, 1064641595005, 3711530969823, 3809130930131, 1113886469524, 81687574006, 0, 0, 0] := by
  rw [show A10K2.u7563 = KTree.node A10K2.t7570 (nat_lit 123315897) (nat_lit 2580542478) (nat_lit 0) A10K2.t7571 from rfl, totK_node, tot7570, tot7571]
  decide +kernel

theorem arows7565 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7565 = true := by
  rw [show A10K2.u7565 = KTree.node A10K2.t7572 (nat_lit 123320493) (nat_lit 6291323306) (nat_lit 0) A10K2.t7573 from rfl, allE_node, rows7572, irow7565, rows7573]
  all_goals rfl

theorem atot7565 : totK PA10K2 A10K2.u7565 = [0, 0, 288340708618, 1959845117586, 3960988379586, 2739899884078, 571469675675, 31082886609, 0, 0] := by
  rw [show A10K2.u7565 = KTree.node A10K2.t7572 (nat_lit 123320493) (nat_lit 6291323306) (nat_lit 0) A10K2.t7573 from rfl, totK_node, tot7572, tot7573]
  decide +kernel

theorem arows7566 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7566 = true := by
  rw [show A10K2.u7566 = KTree.node A10K2.t7574 (nat_lit 123328546) (nat_lit 9062839623) (nat_lit 0) A10K2.t7575 from rfl, allE_node, rows7574, irow7566, rows7575]
  all_goals rfl

theorem atot7566 : totK PA10K2 A10K2.u7566 = [0, 0, 622660509158, 2800639021996, 4012320459099, 1831408722063, 229504266414, 6121173289, 0, 0] := by
  rw [show A10K2.u7566 = KTree.node A10K2.t7574 (nat_lit 123328546) (nat_lit 9062839623) (nat_lit 0) A10K2.t7575 from rfl, totK_node, tot7574, tot7575]
  decide +kernel

theorem arows7569 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7569 = true := by
  rw [show A10K2.u7569 = KTree.node A10K2.t7576 (nat_lit 123334576) (nat_lit 13981672088) (nat_lit 0) A10K2.t7577 from rfl, allE_node, rows7576, irow7569, rows7577]
  all_goals rfl

theorem atot7569 : totK PA10K2 A10K2.u7569 = [0, 578438043648, 2323122498063, 3514966675888, 2739886739828, 930215693069, 76344806208, 0, 0, 0] := by
  rw [show A10K2.u7569 = KTree.node A10K2.t7576 (nat_lit 123334576) (nat_lit 13981672088) (nat_lit 0) A10K2.t7577 from rfl, totK_node, tot7576, tot7577]
  decide +kernel

theorem arows7570 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7570 = true := by
  rw [show A10K2.u7570 = KTree.node A10K2.t7578 (nat_lit 123410432) (nat_lit 15368788893) (nat_lit 0) A10K2.t7579 from rfl, allE_node, rows7578, irow7570, rows7579]
  all_goals rfl

theorem atot7570 : totK PA10K2 A10K2.u7570 = [0, 399046347227, 2299116982770, 4195897197955, 2640455081383, 460568699922, 18355439443, 0, 0, 0] := by
  rw [show A10K2.u7570 = KTree.node A10K2.t7578 (nat_lit 123410432) (nat_lit 15368788893) (nat_lit 0) A10K2.t7579 from rfl, totK_node, tot7578, tot7579]
  decide +kernel

theorem arows7572 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7572 = true := by
  rw [show A10K2.u7572 = KTree.node A10K2.t7580 (nat_lit 123416499) (nat_lit 9302984323) (nat_lit 0) A10K2.t7581 from rfl, allE_node, rows7580, irow7572, rows7581]
  all_goals rfl

theorem atot7572 : totK PA10K2 A10K2.u7572 = [0, 478711658477, 2341002883830, 3939152998266, 2532600378150, 501139294000, 25654631657, 0, 0, 0] := by
  rw [show A10K2.u7572 = KTree.node A10K2.t7580 (nat_lit 123416499) (nat_lit 9302984323) (nat_lit 0) A10K2.t7581 from rfl, totK_node, tot7580, tot7581]
  decide +kernel

theorem arows7573 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7573 = true := by
  rw [show A10K2.u7573 = KTree.node A10K2.t7582 (nat_lit 123430130) (nat_lit 15042214456) (nat_lit 0) A10K2.t7583 from rfl, allE_node, rows7582, irow7573, rows7583]
  all_goals rfl

theorem atot7573 : totK PA10K2 A10K2.u7573 = [0, 883146858471, 3432865461559, 4094633614511, 1497225296793, 156104083177, 6022596713, 0, 0, 0] := by
  rw [show A10K2.u7573 = KTree.node A10K2.t7582 (nat_lit 123430130) (nat_lit 15042214456) (nat_lit 0) A10K2.t7583 from rfl, totK_node, tot7582, tot7583]
  decide +kernel

theorem arows7578 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7578 = true := by
  rw [show A10K2.u7578 = KTree.node A10K2.t7584 (nat_lit 123434653) (nat_lit 5477733542) (nat_lit 0) A10K2.t7585 from rfl, allE_node, rows7584, irow7578, rows7585]
  all_goals rfl

theorem atot7578 : totK PA10K2 A10K2.u7578 = [0, 0, 1113569931977, 3899296672548, 3889584576043, 1071266122643, 62996513375, 0, 0, 0] := by
  rw [show A10K2.u7578 = KTree.node A10K2.t7584 (nat_lit 123434653) (nat_lit 5477733542) (nat_lit 0) A10K2.t7585 from rfl, totK_node, tot7584, tot7585]
  decide +kernel

theorem arows7579 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7579 = true := by
  rw [show A10K2.u7579 = KTree.node A10K2.t7586 (nat_lit 123440718) (nat_lit 10893499012) (nat_lit 0) A10K2.t7587 from rfl, allE_node, rows7586, irow7579, rows7587]
  all_goals rfl

theorem atot7579 : totK PA10K2 A10K2.u7579 = [0, 0, 570317409404, 2768400271635, 4302589919335, 2176233506134, 280366347976, 6904928264, 0, 0] := by
  rw [show A10K2.u7579 = KTree.node A10K2.t7586 (nat_lit 123440718) (nat_lit 10893499012) (nat_lit 0) A10K2.t7587 from rfl, totK_node, tot7586, tot7587]
  decide +kernel

theorem arows7581 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7581 = true := by
  rw [show A10K2.u7581 = KTree.node A10K2.t7588 (nat_lit 123447971) (nat_lit 10480732544) (nat_lit 0) A10K2.t7589 from rfl, allE_node, rows7588, irow7581, rows7589]
  all_goals rfl

theorem atot7581 : totK PA10K2 A10K2.u7581 = [0, 0, 780174937305, 3213483613482, 4078334617376, 1641733073953, 147303468194, 0, 0, 0] := by
  rw [show A10K2.u7581 = KTree.node A10K2.t7588 (nat_lit 123447971) (nat_lit 10480732544) (nat_lit 0) A10K2.t7589 from rfl, totK_node, tot7588, tot7589]
  decide +kernel

theorem arows7582 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7582 = true := by
  rw [show A10K2.u7582 = KTree.node A10K2.t7590 (nat_lit 123462071) (nat_lit 15084722603) (nat_lit 0) A10K2.t7591 from rfl, allE_node, rows7590, irow7582, rows7591]
  all_goals rfl

theorem atot7582 : totK PA10K2 A10K2.u7582 = [0, 0, 708328314987, 2914051256430, 4015757567163, 2022744042324, 280948156632, 7047025452, 0, 0] := by
  rw [show A10K2.u7582 = KTree.node A10K2.t7590 (nat_lit 123462071) (nat_lit 15084722603) (nat_lit 0) A10K2.t7591 from rfl, totK_node, tot7590, tot7591]
  decide +kernel

theorem arows7585 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7585 = true := by
  rw [show A10K2.u7585 = KTree.node A10K2.t7592 (nat_lit 123466628) (nat_lit 7137248409) (nat_lit 0) A10K2.t7593 from rfl, allE_node, rows7592, irow7585, rows7593]
  all_goals rfl

theorem atot7585 : totK PA10K2 A10K2.u7585 = [0, 0, 165887444701, 1728747606769, 4172378255263, 3258352701690, 609923022806, 17977415720, 0, 0] := by
  rw [show A10K2.u7585 = KTree.node A10K2.t7592 (nat_lit 123466628) (nat_lit 7137248409) (nat_lit 0) A10K2.t7593 from rfl, totK_node, tot7592, tot7593]
  decide +kernel

theorem arows7586 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7586 = true := by
  rw [show A10K2.u7586 = KTree.node A10K2.t7594 (nat_lit 123472170) (nat_lit 8695476963) (nat_lit 0) A10K2.t7595 from rfl, allE_node, rows7594, irow7586, rows7595]
  all_goals rfl

theorem atot7586 : totK PA10K2 A10K2.u7586 = [0, 0, 776110475293, 3057505196546, 3801409240126, 1817727167578, 447027728262, 43132710386, 0, 0] := by
  rw [show A10K2.u7586 = KTree.node A10K2.t7594 (nat_lit 123472170) (nat_lit 8695476963) (nat_lit 0) A10K2.t7595 from rfl, totK_node, tot7594, tot7595]
  decide +kernel

theorem arows7588 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7588 = true := by
  rw [show A10K2.u7588 = KTree.node A10K2.t7596 (nat_lit 123494440) (nat_lit 12800366562) (nat_lit 0) A10K2.t7597 from rfl, allE_node, rows7596, irow7588, rows7597]
  all_goals rfl

theorem atot7588 : totK PA10K2 A10K2.u7588 = [0, 0, 609491748306, 2609452285455, 4067535311066, 2410376032518, 426257601161, 13364899180, 0, 0] := by
  rw [show A10K2.u7588 = KTree.node A10K2.t7596 (nat_lit 123494440) (nat_lit 12800366562) (nat_lit 0) A10K2.t7597 from rfl, totK_node, tot7596, tot7597]
  decide +kernel

theorem arows7589 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7589 = true := by
  rw [show A10K2.u7589 = KTree.node A10K2.t7598 (nat_lit 123499079) (nat_lit 9927266953) (nat_lit 0) A10K2.t7599 from rfl, allE_node, rows7598, irow7589, rows7599]
  all_goals rfl

theorem atot7589 : totK PA10K2 A10K2.u7589 = [0, 0, 215095608158, 1784482979100, 4191318377102, 3395011276028, 675855561723, 19122223731, 0, 0] := by
  rw [show A10K2.u7589 = KTree.node A10K2.t7598 (nat_lit 123499079) (nat_lit 9927266953) (nat_lit 0) A10K2.t7599 from rfl, totK_node, tot7598, tot7599]
  decide +kernel

theorem arows7593 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7593 = true := by
  rw [show A10K2.u7593 = KTree.node A10K2.t7600 (nat_lit 123505164) (nat_lit 11580191810) (nat_lit 0) A10K2.t7601 from rfl, allE_node, rows7600, irow7593, rows7601]
  all_goals rfl

theorem atot7593 : totK PA10K2 A10K2.u7593 = [0, 0, 0, 775623392097, 3258627866812, 4221857532025, 1580744030166, 121749189488, 0, 0] := by
  rw [show A10K2.u7593 = KTree.node A10K2.t7600 (nat_lit 123505164) (nat_lit 11580191810) (nat_lit 0) A10K2.t7601 from rfl, totK_node, tot7600, tot7601]
  decide +kernel

theorem arows7594 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7594 = true := by
  rw [show A10K2.u7594 = KTree.node A10K2.t7602 (nat_lit 123527793) (nat_lit 7588473419) (nat_lit 0) A10K2.t7603 from rfl, allE_node, rows7602, irow7594, rows7603]
  all_goals rfl

theorem atot7594 : totK PA10K2 A10K2.u7594 = [0, 0, 0, 823838388709, 3363844711809, 4173449087987, 1584641829920, 187013287410, 7007974415, 0] := by
  rw [show A10K2.u7594 = KTree.node A10K2.t7602 (nat_lit 123527793) (nat_lit 7588473419) (nat_lit 0) A10K2.t7603 from rfl, totK_node, tot7602, tot7603]
  decide +kernel

theorem arows7596 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7596 = true := by
  rw [show A10K2.u7596 = KTree.node A10K2.t7604 (nat_lit 123545874) (nat_lit 14632383213) (nat_lit 0) A10K2.t7605 from rfl, allE_node, rows7604, irow7596, rows7605]
  all_goals rfl

theorem atot7596 : totK PA10K2 A10K2.u7596 = [0, 0, 838891203471, 3192180938260, 3724734773347, 1614459781402, 410588149149, 43720954405, 0, 0] := by
  rw [show A10K2.u7596 = KTree.node A10K2.t7604 (nat_lit 123545874) (nat_lit 14632383213) (nat_lit 0) A10K2.t7605 from rfl, totK_node, tot7604, tot7605]
  decide +kernel

theorem arows7597 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7597 = true := by
  rw [show A10K2.u7597 = KTree.node A10K2.t7606 (nat_lit 123550769) (nat_lit 8125707624) (nat_lit 0) A10K2.t7607 from rfl, allE_node, rows7606, irow7597, rows7607]
  all_goals rfl

theorem atot7597 : totK PA10K2 A10K2.u7597 = [0, 0, 423713582285, 2022464285614, 3737856727548, 2736229041127, 584866263801, 31306924438, 0, 0] := by
  rw [show A10K2.u7597 = KTree.node A10K2.t7606 (nat_lit 123550769) (nat_lit 8125707624) (nat_lit 0) A10K2.t7607 from rfl, totK_node, tot7606, tot7607]
  decide +kernel

theorem arows7600 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7600 = true := by
  rw [show A10K2.u7600 = KTree.node A10K2.t7608 (nat_lit 123558578) (nat_lit 14132138945) (nat_lit 0) A10K2.t7609 from rfl, allE_node, rows7608, irow7600, rows7609]
  all_goals rfl

theorem atot7600 : totK PA10K2 A10K2.u7600 = [0, 0, 601038090043, 2846914865721, 4131562884421, 1822889972806, 228532980688, 6239673734, 0, 0] := by
  rw [show A10K2.u7600 = KTree.node A10K2.t7608 (nat_lit 123558578) (nat_lit 14132138945) (nat_lit 0) A10K2.t7609 from rfl, totK_node, tot7608, tot7609]
  decide +kernel

theorem arows7601 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7601 = true := by
  rw [show A10K2.u7601 = KTree.node A10K2.t7610 (nat_lit 123564550) (nat_lit 14956523810) (nat_lit 0) A10K2.t7611 from rfl, allE_node, rows7610, irow7601, rows7611]
  all_goals rfl

theorem atot7601 : totK PA10K2 A10K2.u7601 = [0, 0, 319364795913, 2106305557136, 4281407964116, 3014939010830, 534212858932, 13242594235, 0, 0] := by
  rw [show A10K2.u7601 = KTree.node A10K2.t7610 (nat_lit 123564550) (nat_lit 14956523810) (nat_lit 0) A10K2.t7611 from rfl, totK_node, tot7610, tot7611]
  decide +kernel

theorem arows7603 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7603 = true := by
  rw [show A10K2.u7603 = KTree.node A10K2.t7612 (nat_lit 123578410) (nat_lit 8971803371) (nat_lit 0) A10K2.t7613 from rfl, allE_node, rows7612, irow7603, rows7613]
  all_goals rfl

theorem atot7603 : totK PA10K2 A10K2.u7603 = [0, 0, 0, 834034036407, 3362682545270, 4097232458636, 1412968576494, 87736822000, 0, 0] := by
  rw [show A10K2.u7603 = KTree.node A10K2.t7612 (nat_lit 123578410) (nat_lit 8971803371) (nat_lit 0) A10K2.t7613 from rfl, totK_node, tot7612, tot7613]
  decide +kernel

theorem arows7604 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7604 = true := by
  rw [show A10K2.u7604 = KTree.node A10K2.t7614 (nat_lit 123583922) (nat_lit 14586405808) (nat_lit 0) A10K2.t7615 from rfl, allE_node, rows7614, irow7604, rows7615]
  all_goals rfl

theorem atot7604 : totK PA10K2 A10K2.u7604 = [0, 0, 0, 727322198656, 2885803400555, 3772181841292, 1871387860899, 303295638102, 7151180950, 0] := by
  rw [show A10K2.u7604 = KTree.node A10K2.t7614 (nat_lit 123583922) (nat_lit 14586405808) (nat_lit 0) A10K2.t7615 from rfl, totK_node, tot7614, tot7615]
  decide +kernel

theorem arows7610 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7610 = true := by
  rw [show A10K2.u7610 = KTree.node A10K2.t7616 (nat_lit 123596165) (nat_lit 2626132121) (nat_lit 0) A10K2.t7617 from rfl, allE_node, rows7616, irow7610, rows7617]
  all_goals rfl

theorem atot7610 : totK PA10K2 A10K2.u7610 = [0, 0, 282573750534, 1617848726210, 3579227630578, 3452431062173, 1085064331382, 68947799775, 0, 0] := by
  rw [show A10K2.u7610 = KTree.node A10K2.t7616 (nat_lit 123596165) (nat_lit 2626132121) (nat_lit 0) A10K2.t7617 from rfl, totK_node, tot7616, tot7617]
  decide +kernel

theorem arows7611 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7611 = true := by
  rw [show A10K2.u7611 = KTree.node A10K2.t7618 (nat_lit 123670849) (nat_lit 10192456253) (nat_lit 0) A10K2.t7619 from rfl, allE_node, rows7618, irow7611, rows7619]
  all_goals rfl

theorem atot7611 : totK PA10K2 A10K2.u7611 = [0, 0, 561221002903, 2565218225048, 4127865686882, 2474356038874, 397955956790, 11991740650, 0, 0] := by
  rw [show A10K2.u7611 = KTree.node A10K2.t7618 (nat_lit 123670849) (nat_lit 10192456253) (nat_lit 0) A10K2.t7619 from rfl, totK_node, tot7618, tot7619]
  decide +kernel

theorem arows7613 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7613 = true := by
  rw [show A10K2.u7613 = KTree.node A10K2.t7620 (nat_lit 123678128) (nat_lit 13631752966) (nat_lit 0) A10K2.t7621 from rfl, allE_node, rows7620, irow7613, rows7621]
  all_goals rfl

theorem atot7613 : totK PA10K2 A10K2.u7613 = [0, 0, 615948692826, 2782929340086, 3992916821575, 2121064183979, 363322306135, 12219140272, 0, 0] := by
  rw [show A10K2.u7613 = KTree.node A10K2.t7620 (nat_lit 123678128) (nat_lit 13631752966) (nat_lit 0) A10K2.t7621 from rfl, totK_node, tot7620, tot7621]
  decide +kernel

theorem arows7614 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7614 = true := by
  rw [show A10K2.u7614 = KTree.node A10K2.t7622 (nat_lit 123691588) (nat_lit 10436837726) (nat_lit 0) A10K2.t7623 from rfl, allE_node, rows7622, irow7614, rows7623]
  all_goals rfl

theorem atot7614 : totK PA10K2 A10K2.u7614 = [0, 0, 850473517516, 3201238664380, 3980033846308, 1750071192385, 163392958744, 0, 0, 0] := by
  rw [show A10K2.u7614 = KTree.node A10K2.t7622 (nat_lit 123691588) (nat_lit 10436837726) (nat_lit 0) A10K2.t7623 from rfl, totK_node, tot7622, tot7623]
  decide +kernel

theorem arows7617 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7617 = true := by
  rw [show A10K2.u7617 = KTree.node A10K2.t7624 (nat_lit 123696318) (nat_lit 15659313499) (nat_lit 0) A10K2.t7625 from rfl, allE_node, rows7624, irow7617, rows7625]
  all_goals rfl

theorem atot7617 : totK PA10K2 A10K2.u7617 = [0, 0, 17179869184, 1397720201959, 4185853905381, 3650532161319, 796505124594, 25509470722, 0, 0] := by
  rw [show A10K2.u7617 = KTree.node A10K2.t7624 (nat_lit 123696318) (nat_lit 15659313499) (nat_lit 0) A10K2.t7625 from rfl, totK_node, tot7624, tot7625]
  decide +kernel

theorem arows7618 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7618 = true := by
  rw [show A10K2.u7618 = KTree.node A10K2.t7626 (nat_lit 123702485) (nat_lit 2528428039) (nat_lit 0) A10K2.t7627 from rfl, allE_node, rows7626, irow7618, rows7627]
  all_goals rfl

theorem atot7618 : totK PA10K2 A10K2.u7618 = [0, 0, 0, 680454974973, 2935716863347, 4130022041401, 1971226119254, 266365084241, 6318667960, 0] := by
  rw [show A10K2.u7618 = KTree.node A10K2.t7626 (nat_lit 123702485) (nat_lit 2528428039) (nat_lit 0) A10K2.t7627 from rfl, totK_node, tot7626, tot7627]
  decide +kernel

theorem arows7620 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7620 = true := by
  rw [show A10K2.u7620 = KTree.node A10K2.t7628 (nat_lit 123709602) (nat_lit 14142712800) (nat_lit 0) A10K2.t7629 from rfl, allE_node, rows7628, irow7620, rows7629]
  all_goals rfl

theorem atot7620 : totK PA10K2 A10K2.u7620 = [0, 0, 0, 778246531629, 3214169561046, 4191693578897, 1635826424955, 130530470574, 0, 0] := by
  rw [show A10K2.u7620 = KTree.node A10K2.t7628 (nat_lit 123709602) (nat_lit 14142712800) (nat_lit 0) A10K2.t7629 from rfl, totK_node, tot7628, tot7629]
  decide +kernel

theorem arows7621 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7621 = true := by
  rw [show A10K2.u7621 = KTree.node A10K2.t7630 (nat_lit 123724172) (nat_lit 7937294420) (nat_lit 0) A10K2.t7631 from rfl, allE_node, rows7630, irow7621, rows7631]
  all_goals rfl

theorem atot7621 : totK PA10K2 A10K2.u7621 = [0, 0, 0, 675710176287, 2947000178640, 4052256675701, 1895141515981, 236558521444, 6439430839, 0] := by
  rw [show A10K2.u7621 = KTree.node A10K2.t7630 (nat_lit 123724172) (nat_lit 7937294420) (nat_lit 0) A10K2.t7631 from rfl, totK_node, tot7630, tot7631]
  decide +kernel

theorem arows7625 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7625 = true := by
  rw [show A10K2.u7625 = KTree.node A10K2.t7632 (nat_lit 123728646) (nat_lit 10667303794) (nat_lit 0) A10K2.t7633 from rfl, allE_node, rows7632, irow7625, rows7633]
  all_goals rfl

theorem atot7625 : totK PA10K2 A10K2.u7625 = [0, 0, 0, 185950034399, 1781033142978, 4133494173114, 3117373538806, 588804170564, 17885676543, 0] := by
  rw [show A10K2.u7625 = KTree.node A10K2.t7632 (nat_lit 123728646) (nat_lit 10667303794) (nat_lit 0) A10K2.t7633 from rfl, totK_node, tot7632, tot7633]
  decide +kernel

theorem arows7626 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7626 = true := by
  rw [show A10K2.u7626 = KTree.node A10K2.t7634 (nat_lit 124332202) (nat_lit 12841543123) (nat_lit 0) A10K2.t7635 from rfl, allE_node, rows7634, irow7626, rows7635]
  all_goals rfl

theorem atot7626 : totK PA10K2 A10K2.u7626 = [0, 0, 872244600920, 3192158952797, 3452403596771, 1261300855987, 654706410228, 372385158108, 43132710386, 0] := by
  rw [show A10K2.u7626 = KTree.node A10K2.t7634 (nat_lit 124332202) (nat_lit 12841543123) (nat_lit 0) A10K2.t7635 from rfl, totK_node, tot7634, tot7635]
  decide +kernel

theorem arows7628 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7628 = true := by
  rw [show A10K2.u7628 = KTree.node A10K2.t7636 (nat_lit 124336804) (nat_lit 13453950136) (nat_lit 0) A10K2.t7637 from rfl, allE_node, rows7636, irow7628, rows7637]
  all_goals rfl

theorem atot7628 : totK PA10K2 A10K2.u7628 = [0, 0, 412332156094, 2050844487197, 3734037012505, 2746054292018, 617774998179, 31768748853, 0, 0] := by
  rw [show A10K2.u7628 = KTree.node A10K2.t7636 (nat_lit 124336804) (nat_lit 13453950136) (nat_lit 0) A10K2.t7637 from rfl, totK_node, tot7636, tot7637]
  decide +kernel

theorem arows7629 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7629 = true := by
  rw [show A10K2.u7629 = KTree.node A10K2.t7638 (nat_lit 124343482) (nat_lit 14904189911) (nat_lit 0) A10K2.t7639 from rfl, allE_node, rows7638, irow7629, rows7639]
  all_goals rfl

theorem atot7629 : totK PA10K2 A10K2.u7629 = [0, 0, 448698520034, 2504291157855, 4164091987063, 2010342176927, 244153003951, 6354482628, 0, 0] := by
  rw [show A10K2.u7629 = KTree.node A10K2.t7638 (nat_lit 124343482) (nat_lit 14904189911) (nat_lit 0) A10K2.t7639 from rfl, totK_node, tot7638, tot7639]
  decide +kernel

theorem arows7632 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7632 = true := by
  rw [show A10K2.u7632 = KTree.node A10K2.t7640 (nat_lit 124349937) (nat_lit 8433814258) (nat_lit 0) A10K2.t7641 from rfl, allE_node, rows7640, irow7632, rows7641]
  all_goals rfl

theorem atot7632 : totK PA10K2 A10K2.u7632 = [0, 0, 610900211470, 2829868795045, 4260211913704, 2203242376499, 289493036863, 0, 0, 0] := by
  rw [show A10K2.u7632 = KTree.node A10K2.t7640 (nat_lit 124349937) (nat_lit 8433814258) (nat_lit 0) A10K2.t7641 from rfl, totK_node, tot7640, tot7641]
  decide +kernel

theorem arows7633 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7633 = true := by
  rw [show A10K2.u7633 = KTree.node A10K2.t7642 (nat_lit 124364022) (nat_lit 15832229186) (nat_lit 0) A10K2.t7643 from rfl, allE_node, rows7642, irow7633, rows7643]
  all_goals rfl

theorem atot7633 : totK PA10K2 A10K2.u7633 = [0, 0, 0, 887237925501, 3505737715647, 4003427589375, 1222717155286, 74019108011, 0, 0] := by
  rw [show A10K2.u7633 = KTree.node A10K2.t7642 (nat_lit 124364022) (nat_lit 15832229186) (nat_lit 0) A10K2.t7643 from rfl, totK_node, tot7642, tot7643]
  decide +kernel

theorem arows7635 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7635 = true := by
  rw [show A10K2.u7635 = KTree.node A10K2.t7644 (nat_lit 124368548) (nat_lit 12524412527) (nat_lit 0) A10K2.t7645 from rfl, allE_node, rows7644, irow7635, rows7645]
  all_goals rfl

theorem atot7635 : totK PA10K2 A10K2.u7635 = [0, 0, 0, 321474566388, 1944829886366, 3952196873874, 2781259941036, 577912885613, 31082886609, 0] := by
  rw [show A10K2.u7635 = KTree.node A10K2.t7644 (nat_lit 124368548) (nat_lit 12524412527) (nat_lit 0) A10K2.t7645 from rfl, totK_node, tot7644, tot7645]
  decide +kernel

theorem arows7636 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7636 = true := by
  rw [show A10K2.u7636 = KTree.node A10K2.t7646 (nat_lit 124373226) (nat_lit 12348202454) (nat_lit 0) A10K2.t7647 from rfl, allE_node, rows7646, irow7636, rows7647]
  all_goals rfl

theorem atot7636 : totK PA10K2 A10K2.u7636 = [0, 0, 0, 652423758713, 3053030481447, 3983044753817, 1382803469856, 103914786332, 0, 0] := by
  rw [show A10K2.u7636 = KTree.node A10K2.t7646 (nat_lit 124373226) (nat_lit 12348202454) (nat_lit 0) A10K2.t7647 from rfl, totK_node, tot7646, tot7647]
  decide +kernel

theorem arows7641 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7641 = true := by
  rw [show A10K2.u7641 = KTree.node A10K2.t7648 (nat_lit 124380900) (nat_lit 11505835311) (nat_lit 0) A10K2.t7649 from rfl, allE_node, rows7648, irow7641, rows7649]
  all_goals rfl

theorem atot7641 : totK PA10K2 A10K2.u7641 = [0, 0, 148618169386, 1140988196381, 3126233569455, 3681160389403, 1574610588717, 197785893846, 6121173289, 0] := by
  rw [show A10K2.u7641 = KTree.node A10K2.t7648 (nat_lit 124380900) (nat_lit 11505835311) (nat_lit 0) A10K2.t7649 from rfl, totK_node, tot7648, tot7649]
  decide +kernel

theorem arows7642 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7642 = true := by
  rw [show A10K2.u7642 = KTree.node A10K2.t7650 (nat_lit 124397636) (nat_lit 11677160244) (nat_lit 0) A10K2.t7651 from rfl, allE_node, rows7650, irow7642, rows7651]
  all_goals rfl

theorem atot7642 : totK PA10K2 A10K2.u7642 = [0, 0, 901404725019, 3593549556121, 4033223747894, 1188403855345, 76049768136, 0, 0, 0] := by
  rw [show A10K2.u7642 = KTree.node A10K2.t7650 (nat_lit 124397636) (nat_lit 11677160244) (nat_lit 0) A10K2.t7651 from rfl, totK_node, tot7650, tot7651]
  decide +kernel

theorem arows7644 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7644 = true := by
  rw [show A10K2.u7644 = KTree.node A10K2.t7652 (nat_lit 124402468) (nat_lit 14079638854) (nat_lit 0) A10K2.t7653 from rfl, allE_node, rows7652, irow7644, rows7653]
  all_goals rfl

theorem atot7644 : totK PA10K2 A10K2.u7644 = [0, 0, 452811472891, 2153710734811, 3780245438509, 2677350940577, 582008470069, 31768748853, 0, 0] := by
  rw [show A10K2.u7644 = KTree.node A10K2.t7652 (nat_lit 124402468) (nat_lit 14079638854) (nat_lit 0) A10K2.t7653 from rfl, totK_node, tot7652, tot7653]
  decide +kernel

theorem arows7645 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7645 = true := by
  rw [show A10K2.u7645 = KTree.node A10K2.t7654 (nat_lit 124409054) (nat_lit 10675672741) (nat_lit 0) A10K2.t7655 from rfl, allE_node, rows7654, irow7645, rows7655]
  all_goals rfl

theorem atot7645 : totK PA10K2 A10K2.u7645 = [0, 0, 290643499251, 2213086224411, 4279122821169, 2264087351422, 262817911619, 6354482628, 0, 0] := by
  rw [show A10K2.u7645 = KTree.node A10K2.t7654 (nat_lit 124409054) (nat_lit 10675672741) (nat_lit 0) A10K2.t7655 from rfl, totK_node, tot7654, tot7655]
  decide +kernel

theorem arows7648 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7648 = true := by
  rw [show A10K2.u7648 = KTree.node A10K2.t7656 (nat_lit 124430573) (nat_lit 5971045383) (nat_lit 0) A10K2.t7657 from rfl, allE_node, rows7656, irow7648, rows7657]
  all_goals rfl

theorem atot7648 : totK PA10K2 A10K2.u7648 = [0, 0, 0, 967739987027, 3734290009292, 3960479259817, 962747956764, 45698881016, 0, 0] := by
  rw [show A10K2.u7648 = KTree.node A10K2.t7656 (nat_lit 124430573) (nat_lit 5971045383) (nat_lit 0) A10K2.t7657 from rfl, totK_node, tot7656, tot7657]
  decide +kernel

theorem arows7649 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7649 = true := by
  rw [show A10K2.u7649 = KTree.node A10K2.t7658 (nat_lit 124439077) (nat_lit 7293157351) (nat_lit 0) A10K2.t7659 from rfl, allE_node, rows7658, irow7649, rows7659]
  all_goals rfl

theorem atot7649 : totK PA10K2 A10K2.u7649 = [0, 0, 0, 568013831436, 2829976264422, 4182872448255, 1556084196692, 129221658424, 0, 0] := by
  rw [show A10K2.u7649 = KTree.node A10K2.t7658 (nat_lit 124439077) (nat_lit 7293157351) (nat_lit 0) A10K2.t7659 from rfl, totK_node, tot7658, tot7659]
  decide +kernel

theorem arows7651 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7651 = true := by
  rw [show A10K2.u7651 = KTree.node A10K2.t7660 (nat_lit 124456844) (nat_lit 6124982003) (nat_lit 0) A10K2.t7661 from rfl, allE_node, rows7660, irow7651, rows7661]
  all_goals rfl

theorem atot7651 : totK PA10K2 A10K2.u7651 = [0, 0, 713069582876, 2893370957214, 3944746498028, 2076584895351, 519193320412, 105543464213, 6354482628, 0] := by
  rw [show A10K2.u7651 = KTree.node A10K2.t7660 (nat_lit 124456844) (nat_lit 6124982003) (nat_lit 0) A10K2.t7661 from rfl, totK_node, tot7660, tot7661]
  decide +kernel

theorem arows7652 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7652 = true := by
  rw [show A10K2.u7652 = KTree.node A10K2.t7662 (nat_lit 124464520) (nat_lit 12763704532) (nat_lit 0) A10K2.t7663 from rfl, allE_node, rows7662, irow7652, rows7663]
  all_goals rfl

theorem atot7652 : totK PA10K2 A10K2.u7652 = [0, 0, 611173185888, 2781578515623, 4056138522482, 2091449415985, 392926641998, 20328650499, 0, 0] := by
  rw [show A10K2.u7652 = KTree.node A10K2.t7662 (nat_lit 124464520) (nat_lit 12763704532) (nat_lit 0) A10K2.t7663 from rfl, totK_node, tot7662, tot7663]
  decide +kernel

theorem arows7656 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7656 = true := by
  rw [show A10K2.u7656 = KTree.node A10K2.t7664 (nat_lit 124477945) (nat_lit 6353373510) (nat_lit 0) A10K2.t7665 from rfl, allE_node, rows7664, irow7656, rows7665]
  all_goals rfl

theorem atot7656 : totK PA10K2 A10K2.u7656 = [0, 0, 738753560848, 2959080521844, 4014795521120, 1992108210380, 282027180274, 11418542001, 0, 0] := by
  rw [show A10K2.u7656 = KTree.node A10K2.t7664 (nat_lit 124477945) (nat_lit 6353373510) (nat_lit 0) A10K2.t7665 from rfl, totK_node, tot7664, tot7665]
  decide +kernel

theorem arows7657 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7657 = true := by
  rw [show A10K2.u7657 = KTree.node A10K2.t7666 (nat_lit 124482780) (nat_lit 10343956648) (nat_lit 0) A10K2.t7667 from rfl, allE_node, rows7666, irow7657, rows7667]
  all_goals rfl

theorem atot7657 : totK PA10K2 A10K2.u7657 = [0, 0, 107440630134, 1485250197001, 4108552327936, 3558283085636, 797237623794, 25405943850, 0, 0] := by
  rw [show A10K2.u7657 = KTree.node A10K2.t7666 (nat_lit 124482780) (nat_lit 10343956648) (nat_lit 0) A10K2.t7667 from rfl, totK_node, tot7666, tot7667]
  decide +kernel

theorem arows7659 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7659 = true := by
  rw [show A10K2.u7659 = KTree.node A10K2.t7668 (nat_lit 124489605) (nat_lit 2437428602) (nat_lit 0) A10K2.t7669 from rfl, allE_node, rows7668, irow7659, rows7669]
  all_goals rfl

theorem atot7659 : totK PA10K2 A10K2.u7659 = [0, 0, 0, 822072228016, 3413882042742, 4205835507263, 1667102965785, 153551154412, 0, 0] := by
  rw [show A10K2.u7659 = KTree.node A10K2.t7668 (nat_lit 124489605) (nat_lit 2437428602) (nat_lit 0) A10K2.t7669 from rfl, totK_node, tot7668, tot7669]
  decide +kernel

theorem arows7660 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7660 = true := by
  rw [show A10K2.u7660 = KTree.node A10K2.t7670 (nat_lit 124497523) (nat_lit 5782390772) (nat_lit 0) A10K2.t7671 from rfl, allE_node, rows7670, irow7660, rows7671]
  all_goals rfl

theorem atot7660 : totK PA10K2 A10K2.u7660 = [0, 0, 0, 501013369758, 2605464700980, 4203452052328, 2213339169733, 300766973761, 7047025452, 0] := by
  rw [show A10K2.u7660 = KTree.node A10K2.t7670 (nat_lit 124497523) (nat_lit 5782390772) (nat_lit 0) A10K2.t7671 from rfl, totK_node, tot7670, tot7671]
  decide +kernel

theorem arows7663 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7663 = true := by
  rw [show A10K2.u7663 = KTree.node A10K2.t7672 (nat_lit 124511729) (nat_lit 7736329609) (nat_lit 0) A10K2.t7673 from rfl, allE_node, rows7672, irow7663, rows7673]
  all_goals rfl

theorem atot7663 : totK PA10K2 A10K2.u7663 = [0, 0, 0, 845483453788, 3366375887172, 4121352605071, 1583693462682, 117482547027, 0, 0] := by
  rw [show A10K2.u7663 = KTree.node A10K2.t7672 (nat_lit 124511729) (nat_lit 7736329609) (nat_lit 0) A10K2.t7673 from rfl, totK_node, tot7672, tot7673]
  decide +kernel

theorem arows7664 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7664 = true := by
  rw [show A10K2.u7664 = KTree.node A10K2.t7674 (nat_lit 124517605) (nat_lit 2525610683) (nat_lit 0) A10K2.t7675 from rfl, allE_node, rows7674, irow7664, rows7675]
  all_goals rfl

theorem atot7664 : totK PA10K2 A10K2.u7664 = [0, 0, 0, 320378530011, 1858722162542, 3818385056510, 3107894548781, 765442327303, 41130295026, 0] := by
  rw [show A10K2.u7664 = KTree.node A10K2.t7674 (nat_lit 124517605) (nat_lit 2525610683) (nat_lit 0) A10K2.t7675 from rfl, totK_node, tot7674, tot7675]
  decide +kernel

theorem arows7666 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7666 = true := by
  rw [show A10K2.u7666 = KTree.node A10K2.t7676 (nat_lit 124595875) (nat_lit 10354898953) (nat_lit 0) A10K2.t7677 from rfl, allE_node, rows7676, irow7666, rows7677]
  all_goals rfl

theorem atot7666 : totK PA10K2 A10K2.u7666 = [0, 0, 0, 544681030302, 2555989766665, 3942343627314, 2174035108804, 422232951198, 25734533292, 0] := by
  rw [show A10K2.u7666 = KTree.node A10K2.t7676 (nat_lit 124595875) (nat_lit 10354898953) (nat_lit 0) A10K2.t7677 from rfl, totK_node, tot7676, tot7677]
  decide +kernel

theorem arows7667 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7667 = true := by
  rw [show A10K2.u7667 = KTree.node A10K2.t7678 (nat_lit 124601613) (nat_lit 5846651114) (nat_lit 0) A10K2.t7679 from rfl, allE_node, rows7678, irow7667, rows7679]
  all_goals rfl

theorem atot7667 : totK PA10K2 A10K2.u7667 = [0, 0, 0, 682009569143, 2861408668576, 3791206643957, 1728873011439, 233579196313, 6034215561, 0] := by
  rw [show A10K2.u7667 = KTree.node A10K2.t7678 (nat_lit 124601613) (nat_lit 5846651114) (nat_lit 0) A10K2.t7679 from rfl, totK_node, tot7678, tot7679]
  decide +kernel

theorem arows7676 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7676 = true := by
  rw [show A10K2.u7676 = KTree.node A10K2.t7680 (nat_lit 124608959) (nat_lit 14252228148) (nat_lit 0) A10K2.t7681 from rfl, allE_node, rows7680, irow7676, rows7681]
  all_goals rfl

theorem atot7676 : totK PA10K2 A10K2.u7676 = [0, 0, 0, 780536075463, 2936625359449, 3917670660305, 1767243320719, 222945324947, 6239673734, 0] := by
  rw [show A10K2.u7676 = KTree.node A10K2.t7680 (nat_lit 124608959) (nat_lit 14252228148) (nat_lit 0) A10K2.t7681 from rfl, totK_node, tot7680, tot7681]
  decide +kernel

theorem arows7677 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7677 = true := by
  rw [show A10K2.u7677 = KTree.node A10K2.t7682 (nat_lit 124614434) (nat_lit 13384554763) (nat_lit 0) A10K2.t7683 from rfl, allE_node, rows7682, irow7677, rows7683]
  all_goals rfl

theorem atot7677 : totK PA10K2 A10K2.u7677 = [0, 0, 0, 0, 1541127125526, 4369356146817, 3346162759195, 674825459236, 35586898073, 0] := by
  rw [show A10K2.u7677 = KTree.node A10K2.t7682 (nat_lit 124614434) (nat_lit 13384554763) (nat_lit 0) A10K2.t7683 from rfl, totK_node, tot7682, tot7683]
  decide +kernel

theorem arows7679 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7679 = true := by
  rw [show A10K2.u7679 = KTree.node A10K2.t7684 (nat_lit 124628420) (nat_lit 952014760) (nat_lit 0) A10K2.t7685 from rfl, allE_node, rows7684, irow7679, rows7685]
  all_goals rfl

theorem atot7679 : totK PA10K2 A10K2.u7679 = [0, 0, 0, 0, 535960473387, 2668835092072, 4034786930493, 2000552734267, 309340112206, 8047840951] := by
  rw [show A10K2.u7679 = KTree.node A10K2.t7684 (nat_lit 124628420) (nat_lit 952014760) (nat_lit 0) A10K2.t7685 from rfl, totK_node, tot7684, tot7685]
  decide +kernel

theorem arows7680 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7680 = true := by
  rw [show A10K2.u7680 = KTree.node A10K2.t7686 (nat_lit 124634988) (nat_lit 11630860357) (nat_lit 0) A10K2.t7687 from rfl, allE_node, rows7686, irow7680, rows7687]
  all_goals rfl

theorem atot7680 : totK PA10K2 A10K2.u7680 = [0, 0, 0, 0, 1146864111140, 3798944263975, 3551846881123, 935893245194, 54672981921, 0] := by
  rw [show A10K2.u7680 = KTree.node A10K2.t7686 (nat_lit 124634988) (nat_lit 11630860357) (nat_lit 0) A10K2.t7687 from rfl, totK_node, tot7686, tot7687]
  decide +kernel

theorem arows7683 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7683 = true := by
  rw [show A10K2.u7683 = KTree.node A10K2.t7688 (nat_lit 124651804) (nat_lit 12157969477) (nat_lit 0) A10K2.t7689 from rfl, allE_node, rows7688, irow7683, rows7689]
  all_goals rfl

theorem atot7683 : totK PA10K2 A10K2.u7683 = [0, 0, 0, 694050188349, 2591339663341, 3526722547470, 2220009872606, 585159437061, 43324002404, 0] := by
  rw [show A10K2.u7683 = KTree.node A10K2.t7688 (nat_lit 124651804) (nat_lit 12157969477) (nat_lit 0) A10K2.t7689 from rfl, totK_node, tot7688, tot7689]
  decide +kernel

theorem arows7684 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7684 = true := by
  rw [show A10K2.u7684 = KTree.node A10K2.t7690 (nat_lit 124663074) (nat_lit 13708722487) (nat_lit 0) A10K2.t7691 from rfl, allE_node, rows7690, irow7684, rows7691]
  all_goals rfl

theorem atot7684 : totK PA10K2 A10K2.u7684 = [0, 0, 0, 522606716403, 2767177249136, 4248654078796, 1921743966512, 225135533623, 6034215561, 0] := by
  rw [show A10K2.u7684 = KTree.node A10K2.t7690 (nat_lit 124663074) (nat_lit 13708722487) (nat_lit 0) A10K2.t7691 from rfl, totK_node, tot7690, tot7691]
  decide +kernel

theorem arows7686 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7686 = true := by
  rw [show A10K2.u7686 = KTree.node A10K2.t7692 (nat_lit 124668229) (nat_lit 6961576414) (nat_lit 0) A10K2.t7693 from rfl, allE_node, rows7692, irow7686, rows7693]
  all_goals rfl

theorem atot7686 : totK PA10K2 A10K2.u7686 = [0, 0, 0, 570531755480, 2945540968566, 4272728533506, 1497238847238, 97810822808, 0, 0] := by
  rw [show A10K2.u7686 = KTree.node A10K2.t7692 (nat_lit 124668229) (nat_lit 6961576414) (nat_lit 0) A10K2.t7693 from rfl, totK_node, tot7692, tot7693]
  decide +kernel

theorem arows7687 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7687 = true := by
  rw [show A10K2.u7687 = KTree.node A10K2.t7694 (nat_lit 124719052) (nat_lit 3313298928) (nat_lit 0) A10K2.t7695 from rfl, allE_node, rows7694, irow7687, rows7695]
  all_goals rfl

theorem atot7687 : totK PA10K2 A10K2.u7687 = [0, 0, 0, 1018983537682, 3505280542329, 3686356885169, 1526636790636, 209210584112, 6354482628, 0] := by
  rw [show A10K2.u7687 = KTree.node A10K2.t7694 (nat_lit 124719052) (nat_lit 3313298928) (nat_lit 0) A10K2.t7695 from rfl, totK_node, tot7694, tot7695]
  decide +kernel

theorem arows7691 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7691 = true := by
  rw [show A10K2.u7691 = KTree.node A10K2.t7696 (nat_lit 124728796) (nat_lit 5411791377) (nat_lit 0) A10K2.t7697 from rfl, allE_node, rows7696, irow7691, rows7697]
  all_goals rfl

theorem atot7691 : totK PA10K2 A10K2.u7691 = [0, 0, 0, 532955257850, 2433203374879, 4019231936260, 2504254115253, 431522505267, 13572172291, 0] := by
  rw [show A10K2.u7691 = KTree.node A10K2.t7696 (nat_lit 124728796) (nat_lit 5411791377) (nat_lit 0) A10K2.t7697 from rfl, totK_node, tot7696, tot7697]
  decide +kernel

theorem arows7692 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7692 = true := by
  rw [show A10K2.u7692 = KTree.node A10K2.t7698 (nat_lit 124743045) (nat_lit 3299367007) (nat_lit 0) A10K2.t7699 from rfl, allE_node, rows7698, irow7692, rows7699]
  all_goals rfl

theorem atot7692 : totK PA10K2 A10K2.u7692 = [0, 0, 0, 610443752422, 3063038024440, 4406600236105, 1885280888393, 185392573708, 0, 0] := by
  rw [show A10K2.u7692 = KTree.node A10K2.t7698 (nat_lit 124743045) (nat_lit 3299367007) (nat_lit 0) A10K2.t7699 from rfl, totK_node, tot7698, tot7699]
  decide +kernel

theorem arows7694 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7694 = true := by
  rw [show A10K2.u7694 = KTree.node A10K2.t7700 (nat_lit 124855680) (nat_lit 6199955476) (nat_lit 0) A10K2.t7701 from rfl, allE_node, rows7700, irow7694, rows7701]
  all_goals rfl

theorem atot7694 : totK PA10K2 A10K2.u7694 = [0, 0, 716119932562, 2354934553181, 2595472391623, 1930764577607, 1649706099310, 534357282439, 41590655314, 0] := by
  rw [show A10K2.u7694 = KTree.node A10K2.t7700 (nat_lit 124855680) (nat_lit 6199955476) (nat_lit 0) A10K2.t7701 from rfl, totK_node, tot7700, tot7701]
  decide +kernel

theorem arows7695 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7695 = true := by
  rw [show A10K2.u7695 = KTree.node A10K2.t7702 (nat_lit 124860193) (nat_lit 6481717644) (nat_lit 0) A10K2.t7703 from rfl, allE_node, rows7702, irow7695, rows7703]
  all_goals rfl

theorem atot7695 : totK PA10K2 A10K2.u7695 = [0, 0, 232324107679, 1796965646905, 4005326735045, 2987367513002, 612792939513, 31768748853, 0, 0] := by
  rw [show A10K2.u7695 = KTree.node A10K2.t7702 (nat_lit 124860193) (nat_lit 6481717644) (nat_lit 0) A10K2.t7703 from rfl, totK_node, tot7702, tot7703]
  decide +kernel

theorem arows7698 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7698 = true := by
  rw [show A10K2.u7698 = KTree.node A10K2.t7704 (nat_lit 124864731) (nat_lit 9756367522) (nat_lit 0) A10K2.t7705 from rfl, allE_node, rows7704, irow7698, rows7705]
  all_goals rfl

theorem atot7698 : totK PA10K2 A10K2.u7698 = [0, 0, 644380375233, 3119906362746, 4205006656791, 1487497626203, 98604486185, 0, 0, 0] := by
  rw [show A10K2.u7698 = KTree.node A10K2.t7704 (nat_lit 124864731) (nat_lit 9756367522) (nat_lit 0) A10K2.t7705 from rfl, totK_node, tot7704, tot7705]
  decide +kernel

theorem arows7699 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7699 = true := by
  rw [show A10K2.u7699 = KTree.node A10K2.t7706 (nat_lit 124873843) (nat_lit 6162812002) (nat_lit 0) A10K2.t7707 from rfl, allE_node, rows7706, irow7699, rows7707]
  all_goals rfl

theorem atot7699 : totK PA10K2 A10K2.u7699 = [0, 0, 595155796918, 2597668903119, 4013597928341, 2362553535710, 404490773413, 13317224979, 0, 0] := by
  rw [show A10K2.u7699 = KTree.node A10K2.t7706 (nat_lit 124873843) (nat_lit 6162812002) (nat_lit 0) A10K2.t7707 from rfl, totK_node, tot7706, tot7707]
  decide +kernel

theorem arows7701 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7701 = true := by
  rw [show A10K2.u7701 = KTree.node A10K2.t7708 (nat_lit 124912232) (nat_lit 12020478838) (nat_lit 0) A10K2.t7709 from rfl, allE_node, rows7708, irow7701, rows7709]
  all_goals rfl

theorem atot7701 : totK PA10K2 A10K2.u7701 = [0, 0, 561156172308, 2606251049688, 4080250617249, 2260048297999, 341760297968, 5963379153, 0, 0] := by
  rw [show A10K2.u7701 = KTree.node A10K2.t7708 (nat_lit 124912232) (nat_lit 12020478838) (nat_lit 0) A10K2.t7709 from rfl, totK_node, tot7708, tot7709]
  decide +kernel

theorem arows7702 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7702 = true := by
  rw [show A10K2.u7702 = KTree.node A10K2.t7710 (nat_lit 124921338) (nat_lit 13350555863) (nat_lit 0) A10K2.t7711 from rfl, allE_node, rows7710, irow7702, rows7711]
  all_goals rfl

theorem atot7702 : totK PA10K2 A10K2.u7702 = [0, 0, 767148028666, 2855393282423, 3670340949096, 1902914636639, 302298718764, 10760911071, 0, 0] := by
  rw [show A10K2.u7702 = KTree.node A10K2.t7710 (nat_lit 124921338) (nat_lit 13350555863) (nat_lit 0) A10K2.t7711 from rfl, totK_node, tot7710, tot7711]
  decide +kernel

theorem arows7707 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7707 = true := by
  rw [show A10K2.u7707 = KTree.node A10K2.t7712 (nat_lit 124926214) (nat_lit 4683817129) (nat_lit 0) A10K2.t7713 from rfl, allE_node, rows7712, irow7707, rows7713]
  all_goals rfl

theorem atot7707 : totK PA10K2 A10K2.u7707 = [0, 0, 239541746934, 1824436531383, 4017033211386, 2892836561714, 538909405493, 31768748853, 0, 0] := by
  rw [show A10K2.u7707 = KTree.node A10K2.t7712 (nat_lit 124926214) (nat_lit 4683817129) (nat_lit 0) A10K2.t7713 from rfl, totK_node, tot7712, tot7713]
  decide +kernel

theorem arows7708 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7708 = true := by
  rw [show A10K2.u7708 = KTree.node A10K2.t7714 (nat_lit 124930615) (nat_lit 4125795129) (nat_lit 0) A10K2.t7715 from rfl, allE_node, rows7714, irow7708, rows7715]
  all_goals rfl

theorem atot7708 : totK PA10K2 A10K2.u7708 = [0, 0, 581282690114, 2889382351025, 4147839211961, 1715568192014, 139115662222, 0, 0, 0] := by
  rw [show A10K2.u7708 = KTree.node A10K2.t7714 (nat_lit 124930615) (nat_lit 4125795129) (nat_lit 0) A10K2.t7715 from rfl, totK_node, tot7714, tot7715]
  decide +kernel

theorem arows7710 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7710 = true := by
  rw [show A10K2.u7710 = KTree.node A10K2.t7716 (nat_lit 124946597) (nat_lit 7321820484) (nat_lit 0) A10K2.t7717 from rfl, allE_node, rows7716, irow7710, rows7717]
  all_goals rfl

theorem atot7710 : totK PA10K2 A10K2.u7710 = [0, 0, 0, 972889732749, 3699283016138, 3814409762392, 922962908170, 49483953819, 0, 0] := by
  rw [show A10K2.u7710 = KTree.node A10K2.t7716 (nat_lit 124946597) (nat_lit 7321820484) (nat_lit 0) A10K2.t7717 from rfl, totK_node, tot7716, tot7717]
  decide +kernel

theorem arows7711 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7711 = true := by
  rw [show A10K2.u7711 = KTree.node A10K2.t7718 (nat_lit 124961313) (nat_lit 10137344356) (nat_lit 0) A10K2.t7719 from rfl, allE_node, rows7718, irow7711, rows7719]
  all_goals rfl

theorem atot7711 : totK PA10K2 A10K2.u7711 = [0, 0, 0, 1171271389783, 3842388493702, 3549862050496, 792803744463, 42620942452, 0, 0] := by
  rw [show A10K2.u7711 = KTree.node A10K2.t7718 (nat_lit 124961313) (nat_lit 10137344356) (nat_lit 0) A10K2.t7719 from rfl, totK_node, tot7718, tot7719]
  decide +kernel

theorem arows7714 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7714 = true := by
  rw [show A10K2.u7714 = KTree.node A10K2.t7720 (nat_lit 124967155) (nat_lit 6282868196) (nat_lit 0) A10K2.t7721 from rfl, allE_node, rows7720, irow7714, rows7721]
  all_goals rfl

theorem atot7714 : totK PA10K2 A10K2.u7714 = [0, 0, 406392106167, 1358626484746, 2559864802512, 3255752066170, 1583885950141, 229924377480, 6354482628, 0] := by
  rw [show A10K2.u7714 = KTree.node A10K2.t7720 (nat_lit 124967155) (nat_lit 6282868196) (nat_lit 0) A10K2.t7721 from rfl, totK_node, tot7720, tot7721]
  decide +kernel

theorem arows7715 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7715 = true := by
  rw [show A10K2.u7715 = KTree.node A10K2.t7722 (nat_lit 125309196) (nat_lit 11846322472) (nat_lit 0) A10K2.t7723 from rfl, allE_node, rows7722, irow7715, rows7723]
  all_goals rfl

theorem atot7715 : totK PA10K2 A10K2.u7715 = [0, 0, 481624067903, 2576223560449, 4225240269291, 2337385062664, 409592801351, 13364899180, 0, 0] := by
  rw [show A10K2.u7715 = KTree.node A10K2.t7722 (nat_lit 125309196) (nat_lit 11846322472) (nat_lit 0) A10K2.t7723 from rfl, totK_node, tot7722, tot7723]
  decide +kernel

theorem arows7717 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7717 = true := by
  rw [show A10K2.u7717 = KTree.node A10K2.t7724 (nat_lit 125332666) (nat_lit 14624595306) (nat_lit 0) A10K2.t7725 from rfl, allE_node, rows7724, irow7717, rows7725]
  all_goals rfl

theorem atot7717 : totK PA10K2 A10K2.u7717 = [0, 0, 714684283898, 3028534295758, 4241504009686, 2012974457612, 275960658124, 6853348008, 0, 0] := by
  rw [show A10K2.u7717 = KTree.node A10K2.t7724 (nat_lit 125332666) (nat_lit 14624595306) (nat_lit 0) A10K2.t7725 from rfl, totK_node, tot7724, tot7725]
  decide +kernel

theorem arows7718 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7718 = true := by
  rw [show A10K2.u7718 = KTree.node A10K2.t7726 (nat_lit 125337495) (nat_lit 14550483610) (nat_lit 0) A10K2.t7727 from rfl, allE_node, rows7726, irow7718, rows7727]
  all_goals rfl

theorem atot7718 : totK PA10K2 A10K2.u7718 = [0, 0, 0, 1126509335596, 3815635761870, 4012763214604, 1144717287007, 69245831368, 0, 0] := by
  rw [show A10K2.u7718 = KTree.node A10K2.t7726 (nat_lit 125337495) (nat_lit 14550483610) (nat_lit 0) A10K2.t7727 from rfl, totK_node, tot7726, tot7727]
  decide +kernel

theorem arows7722 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7722 = true := by
  rw [show A10K2.u7722 = KTree.node A10K2.t7728 (nat_lit 125342600) (nat_lit 14141392688) (nat_lit 0) A10K2.t7729 from rfl, allE_node, rows7728, irow7722, rows7729]
  all_goals rfl

theorem atot7722 : totK PA10K2 A10K2.u7722 = [0, 0, 0, 577388851634, 2869180416500, 4311564619113, 1986142981432, 248112905995, 7237400819, 0] := by
  rw [show A10K2.u7722 = KTree.node A10K2.t7728 (nat_lit 125342600) (nat_lit 14141392688) (nat_lit 0) A10K2.t7729 from rfl, totK_node, tot7728, tot7729]
  decide +kernel

theorem arows7723 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7723 = true := by
  rw [show A10K2.u7723 = KTree.node A10K2.t7730 (nat_lit 125366236) (nat_lit 1819154581) (nat_lit 0) A10K2.t7731 from rfl, allE_node, rows7730, irow7723, rows7731]
  all_goals rfl

theorem atot7723 : totK PA10K2 A10K2.u7723 = [0, 0, 542450728586, 2303164296982, 3605868534066, 2707382042108, 794588304169, 57551169768, 0, 0] := by
  rw [show A10K2.u7723 = KTree.node A10K2.t7730 (nat_lit 125366236) (nat_lit 1819154581) (nat_lit 0) A10K2.t7731 from rfl, totK_node, tot7730, tot7731]
  decide +kernel

theorem arows7725 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7725 = true := by
  rw [show A10K2.u7725 = KTree.node A10K2.t7732 (nat_lit 125384090) (nat_lit 15023698103) (nat_lit 0) A10K2.t7733 from rfl, allE_node, rows7732, irow7725, rows7733]
  all_goals rfl

theorem atot7725 : totK PA10K2 A10K2.u7725 = [0, 0, 296440474885, 1936325244736, 4027896116303, 2870943075787, 594904278021, 31768748853, 0, 0] := by
  rw [show A10K2.u7725 = KTree.node A10K2.t7732 (nat_lit 125384090) (nat_lit 15023698103) (nat_lit 0) A10K2.t7733 from rfl, totK_node, tot7732, tot7733]
  decide +kernel

theorem arows7726 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7726 = true := by
  rw [show A10K2.u7726 = KTree.node A10K2.t7734 (nat_lit 125389469) (nat_lit 5879602105) (nat_lit 0) A10K2.t7735 from rfl, allE_node, rows7734, irow7726, rows7735]
  all_goals rfl

theorem atot7726 : totK PA10K2 A10K2.u7726 = [0, 0, 684752645515, 2800916097189, 3923311460669, 1888737196147, 256553334438, 5982052406, 0, 0] := by
  rw [show A10K2.u7726 = KTree.node A10K2.t7734 (nat_lit 125389469) (nat_lit 5879602105) (nat_lit 0) A10K2.t7735 from rfl, totK_node, tot7734, tot7735]
  decide +kernel

theorem arows7729 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7729 = true := by
  rw [show A10K2.u7729 = KTree.node A10K2.t7736 (nat_lit 125398206) (nat_lit 16105796148) (nat_lit 0) A10K2.t7737 from rfl, allE_node, rows7736, irow7729, rows7737]
  all_goals rfl

theorem atot7729 : totK PA10K2 A10K2.u7729 = [0, 0, 659363822726, 3003643551250, 4259099472053, 2072234043253, 301476650017, 6585347165, 0, 0] := by
  rw [show A10K2.u7729 = KTree.node A10K2.t7736 (nat_lit 125398206) (nat_lit 16105796148) (nat_lit 0) A10K2.t7737 from rfl, totK_node, tot7736, tot7737]
  decide +kernel

theorem arows7730 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7730 = true := by
  rw [show A10K2.u7730 = KTree.node A10K2.t7738 (nat_lit 125403028) (nat_lit 6401852555) (nat_lit 0) A10K2.t7739 from rfl, allE_node, rows7738, irow7730, rows7739]
  all_goals rfl

theorem atot7730 : totK PA10K2 A10K2.u7730 = [0, 0, 0, 1042536165106, 3743290056657, 3837207087971, 1165592302205, 82605879954, 0, 0] := by
  rw [show A10K2.u7730 = KTree.node A10K2.t7738 (nat_lit 125403028) (nat_lit 6401852555) (nat_lit 0) A10K2.t7739 from rfl, totK_node, tot7738, tot7739]
  decide +kernel

theorem arows7732 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7732 = true := by
  rw [show A10K2.u7732 = KTree.node A10K2.t7740 (nat_lit 125416773) (nat_lit 6062813018) (nat_lit 0) A10K2.t7741 from rfl, allE_node, rows7740, irow7732, rows7741]
  all_goals rfl

theorem atot7732 : totK PA10K2 A10K2.u7732 = [0, 0, 0, 295617904848, 2133560778621, 4247311282187, 2550154546787, 428001687428, 13576218110, 0] := by
  rw [show A10K2.u7732 = KTree.node A10K2.t7740 (nat_lit 125416773) (nat_lit 6062813018) (nat_lit 0) A10K2.t7741 from rfl, totK_node, tot7740, tot7741]
  decide +kernel

theorem arows7733 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7733 = true := by
  rw [show A10K2.u7733 = KTree.node A10K2.t7742 (nat_lit 125422371) (nat_lit 9851281029) (nat_lit 0) A10K2.t7743 from rfl, allE_node, rows7742, irow7733, rows7743]
  all_goals rfl

theorem atot7733 : totK PA10K2 A10K2.u7733 = [0, 0, 0, 788516757442, 3230933891209, 4082080163303, 1507346693606, 115124148716, 0, 0] := by
  rw [show A10K2.u7733 = KTree.node A10K2.t7742 (nat_lit 125422371) (nat_lit 9851281029) (nat_lit 0) A10K2.t7743 from rfl, totK_node, tot7742, tot7743]
  decide +kernel

theorem arows7739 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7739 = true := by
  rw [show A10K2.u7739 = KTree.node A10K2.t7744 (nat_lit 125431414) (nat_lit 16179106899) (nat_lit 0) A10K2.t7745 from rfl, allE_node, rows7744, irow7739, rows7745]
  all_goals rfl

theorem atot7739 : totK PA10K2 A10K2.u7739 = [0, 0, 481614459217, 2097663135750, 3594760375909, 2890433622376, 945734889867, 69270120419, 0, 0] := by
  rw [show A10K2.u7739 = KTree.node A10K2.t7744 (nat_lit 125431414) (nat_lit 16179106899) (nat_lit 0) A10K2.t7745 from rfl, totK_node, tot7744, tot7745]
  decide +kernel

theorem arows7740 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7740 = true := by
  rw [show A10K2.u7740 = KTree.node A10K2.t7746 (nat_lit 125506148) (nat_lit 10915091651) (nat_lit 0) A10K2.t7747 from rfl, allE_node, rows7746, irow7740, rows7747]
  all_goals rfl

theorem atot7740 : totK PA10K2 A10K2.u7740 = [0, 0, 503730549693, 2558610259159, 4178706918660, 2419658823686, 399157329963, 12473006693, 0, 0] := by
  rw [show A10K2.u7740 = KTree.node A10K2.t7746 (nat_lit 125506148) (nat_lit 10915091651) (nat_lit 0) A10K2.t7747 from rfl, totK_node, tot7746, tot7747]
  decide +kernel

theorem arows7742 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7742 = true := by
  rw [show A10K2.u7742 = KTree.node A10K2.t7748 (nat_lit 125513401) (nat_lit 5554587333) (nat_lit 0) A10K2.t7749 from rfl, allE_node, rows7748, irow7742, rows7749]
  all_goals rfl

theorem atot7742 : totK PA10K2 A10K2.u7742 = [0, 0, 478711658477, 2413332335522, 4069479096406, 2418077163909, 453184567373, 18682938825, 0, 0] := by
  rw [show A10K2.u7742 = KTree.node A10K2.t7748 (nat_lit 125513401) (nat_lit 5554587333) (nat_lit 0) A10K2.t7749 from rfl, totK_node, tot7748, tot7749]
  decide +kernel

theorem arows7743 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7743 = true := by
  rw [show A10K2.u7743 = KTree.node A10K2.t7750 (nat_lit 125527205) (nat_lit 5559613874) (nat_lit 0) A10K2.t7751 from rfl, allE_node, rows7750, irow7743, rows7751]
  all_goals rfl

theorem atot7743 : totK PA10K2 A10K2.u7743 = [0, 0, 883146858471, 3326843891464, 3972593599509, 1642357833494, 176836448809, 0, 0, 0] := by
  rw [show A10K2.u7743 = KTree.node A10K2.t7750 (nat_lit 125527205) (nat_lit 5559613874) (nat_lit 0) A10K2.t7751 from rfl, totK_node, tot7750, tot7751]
  decide +kernel

theorem arows7746 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7746 = true := by
  rw [show A10K2.u7746 = KTree.node A10K2.t7752 (nat_lit 125531582) (nat_lit 16292101936) (nat_lit 0) A10K2.t7753 from rfl, allE_node, rows7752, irow7746, rows7753]
  all_goals rfl

theorem atot7746 : totK PA10K2 A10K2.u7746 = [0, 0, 0, 1177298115227, 3939567775809, 3834542261930, 1038823989284, 62996513375, 0, 0] := by
  rw [show A10K2.u7746 = KTree.node A10K2.t7752 (nat_lit 125531582) (nat_lit 16292101936) (nat_lit 0) A10K2.t7753 from rfl, totK_node, tot7752, tot7753]
  decide +kernel

theorem arows7747 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7747 = true := by
  rw [show A10K2.u7747 = KTree.node A10K2.t7754 (nat_lit 125537825) (nat_lit 9389332363) (nat_lit 0) A10K2.t7755 from rfl, allE_node, rows7754, irow7747, rows7755]
  all_goals rfl

theorem atot7747 : totK PA10K2 A10K2.u7747 = [0, 0, 0, 611022369721, 2946049489623, 4278202969111, 1951056640783, 243967713743, 6632180018, 0] := by
  rw [show A10K2.u7747 = KTree.node A10K2.t7754 (nat_lit 125537825) (nat_lit 9389332363) (nat_lit 0) A10K2.t7755 from rfl, totK_node, tot7754, tot7755]
  decide +kernel

theorem arows7749 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7749 = true := by
  rw [show A10K2.u7749 = KTree.node A10K2.t7756 (nat_lit 125545117) (nat_lit 5780344690) (nat_lit 0) A10K2.t7757 from rfl, allE_node, rows7756, irow7749, rows7757]
  all_goals rfl

theorem atot7749 : totK PA10K2 A10K2.u7749 = [0, 0, 0, 780174937305, 3215988934968, 4099199547309, 1649358538816, 133026291528, 0, 0] := by
  rw [show A10K2.u7749 = KTree.node A10K2.t7756 (nat_lit 125545117) (nat_lit 5780344690) (nat_lit 0) A10K2.t7757 from rfl, totK_node, tot7756, tot7757]
  decide +kernel

theorem arows7750 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7750 = true := by
  rw [show A10K2.u7750 = KTree.node A10K2.t7758 (nat_lit 125559236) (nat_lit 8190389643) (nat_lit 0) A10K2.t7759 from rfl, allE_node, rows7758, irow7750, rows7759]
  all_goals rfl

theorem atot7750 : totK PA10K2 A10K2.u7750 = [0, 0, 0, 742739948656, 2930396040780, 3981834066543, 1966816495067, 263728180836, 7047025452, 0] := by
  rw [show A10K2.u7750 = KTree.node A10K2.t7758 (nat_lit 125559236) (nat_lit 8190389643) (nat_lit 0) A10K2.t7759 from rfl, totK_node, tot7758, tot7759]
  decide +kernel

theorem arows7754 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7754 = true := by
  rw [show A10K2.u7754 = KTree.node A10K2.t7760 (nat_lit 125563795) (nat_lit 8420291574) (nat_lit 0) A10K2.t7761 from rfl, allE_node, rows7760, irow7754, rows7761]
  all_goals rfl

theorem atot7754 : totK PA10K2 A10K2.u7754 = [0, 0, 0, 122511336145, 1689581135396, 4196127157558, 3267583257607, 631251786183, 17977415720, 0] := by
  rw [show A10K2.u7754 = KTree.node A10K2.t7760 (nat_lit 125563795) (nat_lit 8420291574) (nat_lit 0) A10K2.t7761 from rfl, totK_node, tot7760, tot7761]
  decide +kernel

theorem arows7755 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7755 = true := by
  rw [show A10K2.u7755 = KTree.node A10K2.t7762 (nat_lit 130025684) (nat_lit 6467270909) (nat_lit 0) A10K2.t7763 from rfl, allE_node, rows7762, irow7755, rows7763]
  all_goals rfl

theorem atot7755 : totK PA10K2 A10K2.u7755 = [0, 846984141050, 3149982397311, 3446129135953, 1113531482509, 259809006631, 512267636541, 336461662055, 43132710386, 0] := by
  rw [show A10K2.u7755 = KTree.node A10K2.t7762 (nat_lit 130025684) (nat_lit 6467270909) (nat_lit 0) A10K2.t7763 from rfl, totK_node, tot7762, tot7763]
  decide +kernel

theorem arows7757 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7757 = true := by
  rw [show A10K2.u7757 = KTree.node A10K2.t7764 (nat_lit 130030366) (nat_lit 196335585) (nat_lit 0) A10K2.t7765 from rfl, allE_node, rows7764, irow7757, rows7765]
  all_goals rfl

theorem atot7757 : totK PA10K2 A10K2.u7757 = [0, 348823104215, 1898505417612, 3840463572598, 2757226485903, 580868795725, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u7757 = KTree.node A10K2.t7764 (nat_lit 130030366) (nat_lit 196335585) (nat_lit 0) A10K2.t7765 from rfl, totK_node, tot7764, tot7765]
  decide +kernel

theorem arows7758 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7758 = true := by
  rw [show A10K2.u7758 = KTree.node A10K2.t7766 (nat_lit 130046016) (nat_lit 14686140639) (nat_lit 0) A10K2.t7767 from rfl, allE_node, rows7766, irow7758, rows7767]
  all_goals rfl

theorem atot7758 : totK PA10K2 A10K2.u7758 = [0, 570374893377, 2715361397536, 4007375175753, 1867280147592, 235199306717, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u7758 = KTree.node A10K2.t7766 (nat_lit 130046016) (nat_lit 14686140639) (nat_lit 0) A10K2.t7767 from rfl, totK_node, tot7766, tot7767]
  decide +kernel

theorem arows7761 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7761 = true := by
  rw [show A10K2.u7761 = KTree.node A10K2.t7768 (nat_lit 130052083) (nat_lit 8194827383) (nat_lit 0) A10K2.t7769 from rfl, allE_node, rows7768, irow7761, rows7769]
  all_goals rfl

theorem atot7761 : totK PA10K2 A10K2.u7761 = [0, 465644095695, 2387057908787, 4143183543854, 2722271760233, 529466079257, 13803657628, 0, 0, 0] := by
  rw [show A10K2.u7761 = KTree.node A10K2.t7768 (nat_lit 130052083) (nat_lit 8194827383) (nat_lit 0) A10K2.t7769 from rfl, totK_node, tot7768, tot7769]
  decide +kernel

theorem arows7762 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7762 = true := by
  rw [show A10K2.u7762 = KTree.node A10K2.t7770 (nat_lit 130056760) (nat_lit 14731883437) (nat_lit 0) A10K2.t7771 from rfl, allE_node, rows7770, irow7762, rows7771]
  all_goals rfl

theorem atot7762 : totK PA10K2 A10K2.u7762 = [0, 0, 1052151757357, 3689004252983, 3749940089174, 1074996732780, 80333764819, 0, 0, 0] := by
  rw [show A10K2.u7762 = KTree.node A10K2.t7770 (nat_lit 130056760) (nat_lit 14731883437) (nat_lit 0) A10K2.t7771 from rfl, totK_node, tot7770, tot7771]
  decide +kernel

theorem arows7764 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7764 = true := by
  rw [show A10K2.u7764 = KTree.node A10K2.t7772 (nat_lit 130062445) (nat_lit 5471762042) (nat_lit 0) A10K2.t7773 from rfl, allE_node, rows7772, irow7764, rows7773]
  all_goals rfl

theorem atot7764 : totK PA10K2 A10K2.u7764 = [0, 0, 286854300018, 1988705626673, 3964102423051, 2624168966670, 549802920840, 30650496230, 0, 0] := by
  rw [show A10K2.u7764 = KTree.node A10K2.t7772 (nat_lit 130062445) (nat_lit 5471762042) (nat_lit 0) A10K2.t7773 from rfl, totK_node, tot7772, tot7773]
  decide +kernel

theorem arows7765 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7765 = true := by
  rw [show A10K2.u7765 = KTree.node A10K2.t7774 (nat_lit 130077062) (nat_lit 15169013086) (nat_lit 0) A10K2.t7775 from rfl, allE_node, rows7774, irow7765, rows7775]
  all_goals rfl

theorem atot7765 : totK PA10K2 A10K2.u7765 = [0, 0, 589726196498, 2770227068142, 3983432092700, 1752551335997, 232830030775, 5546304973, 0, 0] := by
  rw [show A10K2.u7765 = KTree.node A10K2.t7774 (nat_lit 130077062) (nat_lit 15169013086) (nat_lit 0) A10K2.t7775 from rfl, totK_node, tot7774, tot7775]
  decide +kernel

theorem arows7770 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7770 = true := by
  rw [show A10K2.u7770 = KTree.node A10K2.t7776 (nat_lit 130084757) (nat_lit 1924608449) (nat_lit 0) A10K2.t7777 from rfl, allE_node, rows7776, irow7770, rows7777]
  all_goals rfl

theorem atot7770 : totK PA10K2 A10K2.u7770 = [0, 539846047986, 2266306728167, 3560402975413, 2757163822251, 834065783178, 57483587606, 0, 0, 0] := by
  rw [show A10K2.u7770 = KTree.node A10K2.t7776 (nat_lit 130084757) (nat_lit 1924608449) (nat_lit 0) A10K2.t7777 from rfl, totK_node, tot7776, tot7777]
  decide +kernel

theorem arows7771 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7771 = true := by
  rw [show A10K2.u7771 = KTree.node A10K2.t7778 (nat_lit 130159136) (nat_lit 14162460222) (nat_lit 0) A10K2.t7779 from rfl, allE_node, rows7778, irow7771, rows7779]
  all_goals rfl

theorem atot7771 : totK PA10K2 A10K2.u7771 = [0, 329166536212, 1937631757748, 4007470042723, 2843652030829, 599887254383, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u7771 = KTree.node A10K2.t7778 (nat_lit 130159136) (nat_lit 14162460222) (nat_lit 0) A10K2.t7779 from rfl, totK_node, tot7778, tot7779]
  decide +kernel

theorem arows7773 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7773 = true := by
  rw [show A10K2.u7773 = KTree.node A10K2.t7780 (nat_lit 130173779) (nat_lit 8881354790) (nat_lit 0) A10K2.t7781 from rfl, allE_node, rows7780, irow7773, rows7781]
  all_goals rfl

theorem atot7773 : totK PA10K2 A10K2.u7773 = [0, 449936922972, 2601166410805, 4205649694622, 2022213168752, 243662400811, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u7773 = KTree.node A10K2.t7780 (nat_lit 130173779) (nat_lit 8881354790) (nat_lit 0) A10K2.t7781 from rfl, totK_node, tot7780, tot7781]
  decide +kernel

theorem arows7774 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7774 = true := by
  rw [show A10K2.u7774 = KTree.node A10K2.t7782 (nat_lit 130190454) (nat_lit 16029065520) (nat_lit 0) A10K2.t7783 from rfl, allE_node, rows7782, irow7774, rows7783]
  all_goals rfl

theorem atot7774 : totK PA10K2 A10K2.u7774 = [0, 0, 997734464520, 3708310667361, 3934538852488, 1031532485686, 63517015118, 0, 0, 0] := by
  rw [show A10K2.u7774 = KTree.node A10K2.t7782 (nat_lit 130190454) (nat_lit 16029065520) (nat_lit 0) A10K2.t7783 from rfl, totK_node, tot7782, tot7783]
  decide +kernel

theorem arows7777 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7777 = true := by
  rw [show A10K2.u7777 = KTree.node A10K2.t7784 (nat_lit 130222085) (nat_lit 6751821106) (nat_lit 0) A10K2.t7785 from rfl, allE_node, rows7784, irow7777, rows7785]
  all_goals rfl

theorem atot7777 : totK PA10K2 A10K2.u7777 = [0, 793104720795, 3007847553862, 3849035172764, 1857128598996, 256345941545, 6356241174, 0, 0, 0] := by
  rw [show A10K2.u7777 = KTree.node A10K2.t7784 (nat_lit 130222085) (nat_lit 6751821106) (nat_lit 0) A10K2.t7785 from rfl, totK_node, tot7784, tot7785]
  decide +kernel

theorem arows7778 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7778 = true := by
  rw [show A10K2.u7778 = KTree.node A10K2.t7786 (nat_lit 130227254) (nat_lit 16407917004) (nat_lit 0) A10K2.t7787 from rfl, allE_node, rows7786, irow7778, rows7787]
  all_goals rfl

theorem atot7778 : totK PA10K2 A10K2.u7778 = [0, 471471247616, 2261173369958, 3895346950339, 2620975436965, 561157516593, 30810868011, 0, 0, 0] := by
  rw [show A10K2.u7778 = KTree.node A10K2.t7786 (nat_lit 130227254) (nat_lit 16407917004) (nat_lit 0) A10K2.t7787 from rfl, totK_node, tot7786, tot7787]
  decide +kernel

theorem arows7780 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7780 = true := by
  rw [show A10K2.u7780 = KTree.node A10K2.t7788 (nat_lit 130234240) (nat_lit 9865657487) (nat_lit 0) A10K2.t7789 from rfl, allE_node, rows7788, irow7780, rows7789]
  all_goals rfl

theorem atot7780 : totK PA10K2 A10K2.u7780 = [0, 494646138789, 2442571721983, 4182126012066, 2500894569335, 449058544085, 18595953933, 0, 0, 0] := by
  rw [show A10K2.u7780 = KTree.node A10K2.t7788 (nat_lit 130234240) (nat_lit 9865657487) (nat_lit 0) A10K2.t7789 from rfl, totK_node, tot7788, tot7789]
  decide +kernel

theorem arows7781 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7781 = true := by
  rw [show A10K2.u7781 = KTree.node A10K2.t7790 (nat_lit 130248404) (nat_lit 8062953466) (nat_lit 0) A10K2.t7791 from rfl, allE_node, rows7790, irow7781, rows7791]
  all_goals rfl

theorem atot7781 : totK PA10K2 A10K2.u7781 = [0, 493242815503, 2562044024975, 4206202767014, 2433135428168, 371806428978, 6853348008, 0, 0, 0] := by
  rw [show A10K2.u7781 = KTree.node A10K2.t7790 (nat_lit 130248404) (nat_lit 8062953466) (nat_lit 0) A10K2.t7791 from rfl, totK_node, tot7790, tot7791]
  decide +kernel

theorem arows7785 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7785 = true := by
  rw [show A10K2.u7785 = KTree.node A10K2.t7792 (nat_lit 130253062) (nat_lit 11738749964) (nat_lit 0) A10K2.t7793 from rfl, allE_node, rows7792, irow7785, rows7793]
  all_goals rfl

theorem atot7785 : totK PA10K2 A10K2.u7785 = [0, 0, 1001162706378, 3632477747192, 3895610659986, 1212650894733, 87223909320, 0, 0, 0] := by
  rw [show A10K2.u7785 = KTree.node A10K2.t7792 (nat_lit 130253062) (nat_lit 11738749964) (nat_lit 0) A10K2.t7793 from rfl, totK_node, tot7792, tot7793]
  decide +kernel

theorem arows7786 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7786 = true := by
  rw [show A10K2.u7786 = KTree.node A10K2.t7794 (nat_lit 130257804) (nat_lit 8419315027) (nat_lit 0) A10K2.t7795 from rfl, allE_node, rows7794, irow7786, rows7795]
  all_goals rfl

theorem atot7786 : totK PA10K2 A10K2.u7786 = [0, 0, 401722206514, 2350985518111, 4276074573190, 2486149302151, 354928440734, 6904928264, 0, 0] := by
  rw [show A10K2.u7786 = KTree.node A10K2.t7794 (nat_lit 130257804) (nat_lit 8419315027) (nat_lit 0) A10K2.t7795 from rfl, totK_node, tot7794, tot7795]
  decide +kernel

theorem arows7788 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7788 = true := by
  rw [show A10K2.u7788 = KTree.node A10K2.t7796 (nat_lit 130266525) (nat_lit 4937867844) (nat_lit 0) A10K2.t7797 from rfl, allE_node, rows7796, irow7788, rows7797]
  all_goals rfl

theorem atot7788 : totK PA10K2 A10K2.u7788 = [0, 0, 592503457474, 2721950088617, 4199086353841, 2308737051499, 309504133402, 7047025452, 0, 0] := by
  rw [show A10K2.u7788 = KTree.node A10K2.t7796 (nat_lit 130266525) (nat_lit 4937867844) (nat_lit 0) A10K2.t7797 from rfl, totK_node, tot7796, tot7797]
  decide +kernel

theorem arows7789 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7789 = true := by
  rw [show A10K2.u7789 = KTree.node A10K2.t7798 (nat_lit 130280917) (nat_lit 3343945921) (nat_lit 0) A10K2.t7799 from rfl, allE_node, rows7798, irow7789, rows7799]
  all_goals rfl

theorem atot7789 : totK PA10K2 A10K2.u7789 = [0, 0, 581583812515, 2700994775310, 4107499531362, 2190828029539, 280136798969, 6066958478, 0, 0] := by
  rw [show A10K2.u7789 = KTree.node A10K2.t7798 (nat_lit 130280917) (nat_lit 3343945921) (nat_lit 0) A10K2.t7799 from rfl, totK_node, tot7798, tot7799]
  decide +kernel

theorem arows7792 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7792 = true := by
  rw [show A10K2.u7792 = KTree.node A10K2.t7800 (nat_lit 130285523) (nat_lit 8572954976) (nat_lit 0) A10K2.t7801 from rfl, allE_node, rows7800, irow7792, rows7801]
  all_goals rfl

theorem atot7792 : totK PA10K2 A10K2.u7792 = [0, 0, 554885253651, 2332583371668, 3530820340532, 2553979750273, 737797410017, 55043167628, 0, 0] := by
  rw [show A10K2.u7792 = KTree.node A10K2.t7800 (nat_lit 130285523) (nat_lit 8572954976) (nat_lit 0) A10K2.t7801 from rfl, totK_node, tot7800, tot7801]
  decide +kernel

theorem arows7793 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7793 = true := by
  rw [show A10K2.u7793 = KTree.node A10K2.t7802 (nat_lit 130290019) (nat_lit 4974368183) (nat_lit 0) A10K2.t7803 from rfl, allE_node, rows7802, irow7793, rows7803]
  all_goals rfl

theorem atot7793 : totK PA10K2 A10K2.u7793 = [0, 0, 292098887399, 1940595047731, 3971827664704, 2700369130325, 556456524180, 30831673886, 0, 0] := by
  rw [show A10K2.u7793 = KTree.node A10K2.t7802 (nat_lit 130290019) (nat_lit 4974368183) (nat_lit 0) A10K2.t7803 from rfl, totK_node, tot7802, tot7803]
  decide +kernel

theorem arows7795 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7795 = true := by
  rw [show A10K2.u7795 = KTree.node A10K2.t7804 (nat_lit 130304165) (nat_lit 7333572875) (nat_lit 0) A10K2.t7805 from rfl, allE_node, rows7804, irow7795, rows7805]
  all_goals rfl

theorem atot7795 : totK PA10K2 A10K2.u7795 = [0, 0, 582481005154, 2827442465534, 4158825136129, 1708567467902, 153068856024, 0, 0, 0] := by
  rw [show A10K2.u7795 = KTree.node A10K2.t7804 (nat_lit 130304165) (nat_lit 7333572875) (nat_lit 0) A10K2.t7805 from rfl, totK_node, tot7804, tot7805]
  decide +kernel

theorem arows7796 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7796 = true := by
  rw [show A10K2.u7796 = KTree.node A10K2.t7806 (nat_lit 130311890) (nat_lit 15162462724) (nat_lit 0) A10K2.t7807 from rfl, allE_node, rows7806, irow7796, rows7807]
  all_goals rfl

theorem atot7796 : totK PA10K2 A10K2.u7796 = [0, 0, 802361088133, 3173025865597, 4014319680715, 1734230184338, 217339502986, 5705019915, 0, 0] := by
  rw [show A10K2.u7796 = KTree.node A10K2.t7806 (nat_lit 130311890) (nat_lit 15162462724) (nat_lit 0) A10K2.t7807 from rfl, totK_node, tot7806, tot7807]
  decide +kernel

theorem arows7803 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7803 = true := by
  rw [show A10K2.u7803 = KTree.node A10K2.t7808 (nat_lit 130318011) (nat_lit 6438770386) (nat_lit 0) A10K2.t7809 from rfl, allE_node, rows7808, irow7803, rows7809]
  all_goals rfl

theorem atot7803 : totK PA10K2 A10K2.u7803 = [0, 0, 0, 1123100119177, 3865514361679, 3811536178092, 1012064837940, 60698249753, 0, 0] := by
  rw [show A10K2.u7803 = KTree.node A10K2.t7808 (nat_lit 130318011) (nat_lit 6438770386) (nat_lit 0) A10K2.t7809 from rfl, totK_node, tot7808, tot7809]
  decide +kernel

theorem arows7804 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7804 = true := by
  rw [show A10K2.u7804 = KTree.node A10K2.t7810 (nat_lit 130322787) (nat_lit 4652171420) (nat_lit 0) A10K2.t7811 from rfl, allE_node, rows7810, irow7804, rows7811]
  all_goals rfl

theorem atot7804 : totK PA10K2 A10K2.u7804 = [0, 0, 0, 286915412457, 2128694869669, 4118401309126, 2393074941008, 411353267670, 13364899180, 0] := by
  rw [show A10K2.u7804 = KTree.node A10K2.t7810 (nat_lit 130322787) (nat_lit 4652171420) (nat_lit 0) A10K2.t7811 from rfl, totK_node, tot7810, tot7811]
  decide +kernel

theorem arows7806 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7806 = true := by
  rw [show A10K2.u7806 = KTree.node A10K2.t7812 (nat_lit 130337313) (nat_lit 9993601451) (nat_lit 0) A10K2.t7813 from rfl, allE_node, rows7812, irow7806, rows7813]
  all_goals rfl

theorem atot7806 : totK PA10K2 A10K2.u7806 = [0, 0, 0, 870828675635, 3327799780580, 3768272666528, 1255938437871, 107054969576, 0, 0] := by
  rw [show A10K2.u7806 = KTree.node A10K2.t7812 (nat_lit 130337313) (nat_lit 9993601451) (nat_lit 0) A10K2.t7813 from rfl, totK_node, tot7812, tot7813]
  decide +kernel

theorem arows7807 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7807 = true := by
  rw [show A10K2.u7807 = KTree.node A10K2.t7814 (nat_lit 130346958) (nat_lit 13580271840) (nat_lit 0) A10K2.t7815 from rfl, allE_node, rows7814, irow7807, rows7815]
  all_goals rfl

theorem atot7807 : totK PA10K2 A10K2.u7807 = [0, 0, 539669932579, 2383202478010, 3743232216929, 2621923201004, 645393629108, 43911449185, 0, 0] := by
  rw [show A10K2.u7807 = KTree.node A10K2.t7814 (nat_lit 130346958) (nat_lit 13580271840) (nat_lit 0) A10K2.t7815 from rfl, totK_node, tot7814, tot7815]
  decide +kernel

theorem arows7810 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7810 = true := by
  rw [show A10K2.u7810 = KTree.node A10K2.t7816 (nat_lit 130421362) (nat_lit 4907721889) (nat_lit 0) A10K2.t7817 from rfl, allE_node, rows7816, irow7810, rows7817]
  all_goals rfl

theorem atot7810 : totK PA10K2 A10K2.u7810 = [0, 0, 403060329347, 2018158348455, 3918413379973, 2726588674598, 570533025695, 30831673886, 0, 0] := by
  rw [show A10K2.u7810 = KTree.node A10K2.t7816 (nat_lit 130421362) (nat_lit 4907721889) (nat_lit 0) A10K2.t7817 from rfl, totK_node, tot7816, tot7817]
  decide +kernel

theorem arows7811 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7811 = true := by
  rw [show A10K2.u7811 = KTree.node A10K2.t7818 (nat_lit 130437191) (nat_lit 10164890560) (nat_lit 0) A10K2.t7819 from rfl, allE_node, rows7818, irow7811, rows7819]
  all_goals rfl

theorem atot7811 : totK PA10K2 A10K2.u7811 = [0, 0, 375344432939, 2487688898924, 4330387234824, 2061625117570, 249909670979, 6354482628, 0, 0] := by
  rw [show A10K2.u7811 = KTree.node A10K2.t7818 (nat_lit 130437191) (nat_lit 10164890560) (nat_lit 0) A10K2.t7819 from rfl, totK_node, tot7818, tot7819]
  decide +kernel

theorem arows7813 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7813 = true := by
  rw [show A10K2.u7813 = KTree.node A10K2.t7820 (nat_lit 130452986) (nat_lit 8611006411) (nat_lit 0) A10K2.t7821 from rfl, allE_node, rows7820, irow7813, rows7821]
  all_goals rfl

theorem atot7813 : totK PA10K2 A10K2.u7813 = [0, 0, 0, 1007758434012, 3720750492572, 3831296142602, 964751718050, 49284168630, 0, 0] := by
  rw [show A10K2.u7813 = KTree.node A10K2.t7820 (nat_lit 130452986) (nat_lit 8611006411) (nat_lit 0) A10K2.t7821 from rfl, totK_node, tot7820, tot7821]
  decide +kernel

theorem arows7814 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7814 = true := by
  rw [show A10K2.u7814 = KTree.node A10K2.t7822 (nat_lit 130484516) (nat_lit 14051435791) (nat_lit 0) A10K2.t7823 from rfl, allE_node, rows7822, irow7814, rows7823]
  all_goals rfl

theorem atot7814 : totK PA10K2 A10K2.u7814 = [0, 0, 793104720795, 3062007800449, 3860359411365, 1822693896070, 263980722179, 6356241174, 0, 0] := by
  rw [show A10K2.u7814 = KTree.node A10K2.t7822 (nat_lit 130484516) (nat_lit 14051435791) (nat_lit 0) A10K2.t7823 from rfl, totK_node, tot7822, tot7823]
  decide +kernel

theorem arows7818 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7818 = true := by
  rw [show A10K2.u7818 = KTree.node A10K2.t7824 (nat_lit 130491555) (nat_lit 10628298838) (nat_lit 0) A10K2.t7825 from rfl, allE_node, rows7824, irow7818, rows7825]
  all_goals rfl

theorem atot7818 : totK PA10K2 A10K2.u7818 = [0, 0, 590588076907, 2683179244241, 4029965483143, 2215811775974, 409927135130, 18457393337, 0, 0] := by
  rw [show A10K2.u7818 = KTree.node A10K2.t7824 (nat_lit 130491555) (nat_lit 10628298838) (nat_lit 0) A10K2.t7825 from rfl, totK_node, tot7824, tot7825]
  decide +kernel

theorem arows7819 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7819 = true := by
  rw [show A10K2.u7819 = KTree.node A10K2.t7826 (nat_lit 130498038) (nat_lit 16825448452) (nat_lit 0) A10K2.t7827 from rfl, allE_node, rows7826, irow7819, rows7827]
  all_goals rfl

theorem atot7819 : totK PA10K2 A10K2.u7819 = [0, 0, 540757303387, 2582550125078, 4201723165789, 2372116011122, 331863895613, 7151180950, 0, 0] := by
  rw [show A10K2.u7819 = KTree.node A10K2.t7826 (nat_lit 130498038) (nat_lit 16825448452) (nat_lit 0) A10K2.t7827 from rfl, totK_node, tot7826, tot7827]
  decide +kernel

theorem arows7821 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7821 = true := by
  rw [show A10K2.u7821 = KTree.node A10K2.t7828 (nat_lit 130511241) (nat_lit 9534329249) (nat_lit 0) A10K2.t7829 from rfl, allE_node, rows7828, irow7821, rows7829]
  all_goals rfl

theorem atot7821 : totK PA10K2 A10K2.u7821 = [0, 0, 327737319032, 2080994963456, 4213577647178, 2906027572576, 514040192646, 13231026584, 0, 0] := by
  rw [show A10K2.u7821 = KTree.node A10K2.t7828 (nat_lit 130511241) (nat_lit 9534329249) (nat_lit 0) A10K2.t7829 from rfl, totK_node, tot7828, tot7829]
  decide +kernel

theorem arows7822 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7822 = true := by
  rw [show A10K2.u7822 = KTree.node A10K2.t7830 (nat_lit 130623274) (nat_lit 12526482812) (nat_lit 0) A10K2.t7831 from rfl, allE_node, rows7830, irow7822, rows7831]
  all_goals rfl

theorem atot7822 : totK PA10K2 A10K2.u7822 = [0, 849876618421, 2929360963130, 2958587760139, 1376599983262, 1111256192206, 507418605586, 49137536365, 0, 0] := by
  rw [show A10K2.u7822 = KTree.node A10K2.t7830 (nat_lit 130623274) (nat_lit 12526482812) (nat_lit 0) A10K2.t7831 from rfl, totK_node, tot7830, tot7831]
  decide +kernel

theorem arows7825 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7825 = true := by
  rw [show A10K2.u7825 = KTree.node A10K2.t7832 (nat_lit 130627813) (nat_lit 7110780310) (nat_lit 0) A10K2.t7833 from rfl, allE_node, rows7832, irow7825, rows7833]
  all_goals rfl

theorem atot7825 : totK PA10K2 A10K2.u7825 = [0, 269380288048, 1802693608266, 3875456908574, 2963793752166, 627427233397, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u7825 = KTree.node A10K2.t7832 (nat_lit 130627813) (nat_lit 7110780310) (nat_lit 0) A10K2.t7833 from rfl, totK_node, tot7832, tot7833]
  decide +kernel

theorem arows7826 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7826 = true := by
  rw [show A10K2.u7826 = KTree.node A10K2.t7834 (nat_lit 130634980) (nat_lit 13288066281) (nat_lit 0) A10K2.t7835 from rfl, allE_node, rows7834, irow7826, rows7835]
  all_goals rfl

theorem atot7826 : totK PA10K2 A10K2.u7826 = [0, 505740865135, 2647816451325, 4194338421856, 1992387809355, 245444102597, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u7826 = KTree.node A10K2.t7834 (nat_lit 130634980) (nat_lit 13288066281) (nat_lit 0) A10K2.t7835 from rfl, totK_node, tot7834, tot7835]
  decide +kernel

theorem arows7828 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7828 = true := by
  rw [show A10K2.u7828 = KTree.node A10K2.t7836 (nat_lit 130641465) (nat_lit 6987014221) (nat_lit 0) A10K2.t7837 from rfl, allE_node, rows7836, irow7828, rows7837]
  all_goals rfl

theorem atot7828 : totK PA10K2 A10K2.u7828 = [0, 613166546329, 2741850810500, 4178694543897, 2301082932016, 356889843917, 6840736825, 0, 0, 0] := by
  rw [show A10K2.u7828 = KTree.node A10K2.t7836 (nat_lit 130641465) (nat_lit 6987014221) (nat_lit 0) A10K2.t7837 from rfl, totK_node, tot7836, tot7837]
  decide +kernel

theorem arows7829 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7829 = true := by
  rw [show A10K2.u7829 = KTree.node A10K2.t7838 (nat_lit 130655509) (nat_lit 6901166278) (nat_lit 0) A10K2.t7839 from rfl, allE_node, rows7838, irow7829, rows7839]
  all_goals rfl

theorem atot7829 : totK PA10K2 A10K2.u7829 = [0, 0, 936054336640, 3492019027483, 3906751151943, 1242756640745, 88594092409, 0, 0, 0] := by
  rw [show A10K2.u7829 = KTree.node A10K2.t7838 (nat_lit 130655509) (nat_lit 6901166278) (nat_lit 0) A10K2.t7839 from rfl, totK_node, tot7838, tot7839]
  decide +kernel

theorem arows7834 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7834 = true := by
  rw [show A10K2.u7834 = KTree.node A10K2.t7840 (nat_lit 130660054) (nat_lit 13153357165) (nat_lit 0) A10K2.t7841 from rfl, allE_node, rows7840, irow7834, rows7841]
  all_goals rfl

theorem atot7834 : totK PA10K2 A10K2.u7834 = [0, 0, 286576173371, 1986580533991, 3975305515001, 2739953500758, 571868449210, 31082886609, 0, 0] := by
  rw [show A10K2.u7834 = KTree.node A10K2.t7840 (nat_lit 130660054) (nat_lit 13153357165) (nat_lit 0) A10K2.t7841 from rfl, totK_node, tot7840, tot7841]
  decide +kernel

theorem arows7835 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7835 = true := by
  rw [show A10K2.u7835 = KTree.node A10K2.t7842 (nat_lit 130665230) (nat_lit 17340992) (nat_lit 0) A10K2.t7843 from rfl, allE_node, rows7842, irow7835, rows7843]
  all_goals rfl

theorem atot7835 : totK PA10K2 A10K2.u7835 = [0, 0, 622865460960, 2763363008367, 3953835478101, 1777148031903, 228655978291, 6121173289, 0, 0] := by
  rw [show A10K2.u7835 = KTree.node A10K2.t7842 (nat_lit 130665230) (nat_lit 17340992) (nat_lit 0) A10K2.t7843 from rfl, totK_node, tot7842, tot7843]
  decide +kernel

theorem arows7837 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7837 = true := by
  rw [show A10K2.u7837 = KTree.node A10K2.t7844 (nat_lit 130673849) (nat_lit 5947340225) (nat_lit 0) A10K2.t7845 from rfl, allE_node, rows7844, irow7837, rows7845]
  all_goals rfl

theorem atot7837 : totK PA10K2 A10K2.u7837 = [0, 304922396905, 1620408871420, 3532131441212, 3423765060054, 1135696801927, 83242703312, 0, 0, 0] := by
  rw [show A10K2.u7837 = KTree.node A10K2.t7844 (nat_lit 130673849) (nat_lit 5947340225) (nat_lit 0) A10K2.t7845 from rfl, totK_node, tot7844, tot7845]
  decide +kernel

theorem arows7838 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7838 = true := by
  rw [show A10K2.u7838 = KTree.node A10K2.t7846 (nat_lit 130690999) (nat_lit 15100918269) (nat_lit 0) A10K2.t7847 from rfl, allE_node, rows7846, irow7838, rows7847]
  all_goals rfl

theorem atot7838 : totK PA10K2 A10K2.u7838 = [0, 457794405310, 2403327261462, 4075554810783, 2375709908957, 460710443833, 25734533292, 0, 0, 0] := by
  rw [show A10K2.u7838 = KTree.node A10K2.t7846 (nat_lit 130690999) (nat_lit 15100918269) (nat_lit 0) A10K2.t7847 from rfl, totK_node, tot7846, tot7847]
  decide +kernel

theorem arows7841 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7841 = true := by
  rw [show A10K2.u7841 = KTree.node A10K2.t7848 (nat_lit 130697287) (nat_lit 5708825720) (nat_lit 128) A10K2.t7849 from rfl, allE_node, rows7848, irow7841, rows7849]
  all_goals rfl

theorem atot7841 : totK PA10K2 A10K2.u7841 = [0, 561217355197, 2781256613783, 4117918339676, 2008062010048, 260543609991, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u7841 = KTree.node A10K2.t7848 (nat_lit 130697287) (nat_lit 5708825720) (nat_lit 128) A10K2.t7849 from rfl, totK_node, tot7848, tot7849]
  decide +kernel

theorem arows7842 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7842 = true := by
  rw [show A10K2.u7842 = KTree.node A10K2.t7850 (nat_lit 130722002) (nat_lit 15339778260) (nat_lit 0) A10K2.t7851 from rfl, allE_node, rows7850, irow7842, rows7851]
  all_goals rfl

theorem atot7842 : totK PA10K2 A10K2.u7842 = [0, 0, 1048847786719, 3851557291956, 3873947150080, 941407824207, 45698759736, 0, 0, 0] := by
  rw [show A10K2.u7842 = KTree.node A10K2.t7850 (nat_lit 130722002) (nat_lit 15339778260) (nat_lit 0) A10K2.t7851 from rfl, totK_node, tot7850, tot7851]
  decide +kernel

theorem arows7844 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7844 = true := by
  rw [show A10K2.u7844 = KTree.node A10K2.t7852 (nat_lit 130744616) (nat_lit 12390657786) (nat_lit 0) A10K2.t7853 from rfl, allE_node, rows7852, irow7844, rows7853]
  all_goals rfl

theorem atot7844 : totK PA10K2 A10K2.u7844 = [0, 588716830688, 2475173535165, 3810144652026, 2475148933042, 521072502002, 31889781550, 0, 0, 0] := by
  rw [show A10K2.u7844 = KTree.node A10K2.t7852 (nat_lit 130744616) (nat_lit 12390657786) (nat_lit 0) A10K2.t7853 from rfl, totK_node, tot7852, tot7853]
  decide +kernel

theorem arows7845 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7845 = true := by
  rw [show A10K2.u7845 = KTree.node A10K2.t7854 (nat_lit 130753746) (nat_lit 15688061821) (nat_lit 0) A10K2.t7855 from rfl, allE_node, rows7854, irow7845, rows7855]
  all_goals rfl

theorem atot7845 : totK PA10K2 A10K2.u7845 = [0, 610215587680, 2623117074416, 3938666370144, 2251144385148, 425119400679, 18342047509, 0, 0, 0] := by
  rw [show A10K2.u7845 = KTree.node A10K2.t7854 (nat_lit 130753746) (nat_lit 15688061821) (nat_lit 0) A10K2.t7855 from rfl, totK_node, tot7854, tot7855]
  decide +kernel

theorem arows7849 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7849 = true := by
  rw [show A10K2.u7849 = KTree.node A10K2.t7856 (nat_lit 130758370) (nat_lit 13703502204) (nat_lit 0) A10K2.t7857 from rfl, allE_node, rows7856, irow7849, rows7857]
  all_goals rfl

theorem atot7849 : totK PA10K2 A10K2.u7849 = [0, 325146662527, 1989393384427, 4009202339646, 2901187819192, 604781503956, 31747192500, 0, 0, 0] := by
  rw [show A10K2.u7849 = KTree.node A10K2.t7856 (nat_lit 130758370) (nat_lit 13703502204) (nat_lit 0) A10K2.t7857 from rfl, totK_node, tot7856, tot7857]
  decide +kernel

theorem arows7850 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7850 = true := by
  rw [show A10K2.u7850 = KTree.node A10K2.t7858 (nat_lit 130772038) (nat_lit 15221459860) (nat_lit 0) A10K2.t7859 from rfl, allE_node, rows7858, irow7850, rows7859]
  all_goals rfl

theorem atot7850 : totK PA10K2 A10K2.u7850 = [0, 729546915273, 3110937761406, 4193519497135, 1834158180703, 190070472090, 0, 0, 0, 0] := by
  rw [show A10K2.u7850 = KTree.node A10K2.t7858 (nat_lit 130772038) (nat_lit 15221459860) (nat_lit 0) A10K2.t7859 from rfl, totK_node, tot7858, tot7859]
  decide +kernel

theorem arows7852 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7852 = true := by
  rw [show A10K2.u7852 = KTree.node A10K2.t7860 (nat_lit 130776577) (nat_lit 10304730047) (nat_lit 0) A10K2.t7861 from rfl, allE_node, rows7860, irow7852, rows7861]
  all_goals rfl

theorem atot7852 : totK PA10K2 A10K2.u7852 = [0, 0, 1000649649587, 3687788561974, 4029837536904, 1249575860774, 81401727931, 0, 0, 0] := by
  rw [show A10K2.u7852 = KTree.node A10K2.t7860 (nat_lit 130776577) (nat_lit 10304730047) (nat_lit 0) A10K2.t7861 from rfl, totK_node, tot7860, tot7861]
  decide +kernel

theorem arows7853 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7853 = true := by
  rw [show A10K2.u7853 = KTree.node A10K2.t7862 (nat_lit 130781992) (nat_lit 11693238585) (nat_lit 0) A10K2.t7863 from rfl, allE_node, rows7862, irow7853, rows7863]
  all_goals rfl

theorem atot7853 : totK PA10K2 A10K2.u7853 = [0, 0, 509247950110, 2560417390818, 4228338577230, 2371498439596, 332529226112, 6904928264, 0, 0] := by
  rw [show A10K2.u7853 = KTree.node A10K2.t7862 (nat_lit 130781992) (nat_lit 11693238585) (nat_lit 0) A10K2.t7863 from rfl, totK_node, tot7862, tot7863]
  decide +kernel

theorem arows7856 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7856 = true := by
  rw [show A10K2.u7856 = KTree.node A10K2.t7864 (nat_lit 130789366) (nat_lit 16691704329) (nat_lit 0) A10K2.t7865 from rfl, allE_node, rows7864, irow7856, rows7865]
  all_goals rfl

theorem atot7856 : totK PA10K2 A10K2.u7856 = [0, 0, 487588809585, 2574762933461, 4198181481096, 2285388633114, 307196531697, 7047025452, 0, 0] := by
  rw [show A10K2.u7856 = KTree.node A10K2.t7864 (nat_lit 130789366) (nat_lit 16691704329) (nat_lit 0) A10K2.t7865 from rfl, totK_node, tot7864, tot7865]
  decide +kernel

theorem arows7857 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7857 = true := by
  rw [show A10K2.u7857 = KTree.node A10K2.t7866 (nat_lit 130803490) (nat_lit 13428283502) (nat_lit 0) A10K2.t7867 from rfl, allE_node, rows7866, irow7857, rows7867]
  all_goals rfl

theorem atot7857 : totK PA10K2 A10K2.u7857 = [0, 0, 867939915310, 3380223960059, 4048476791616, 1510817054123, 119240249289, 0, 0, 0] := by
  rw [show A10K2.u7857 = KTree.node A10K2.t7866 (nat_lit 130803490) (nat_lit 13428283502) (nat_lit 0) A10K2.t7867 from rfl, totK_node, tot7866, tot7867]
  decide +kernel

theorem arows7859 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7859 = true := by
  rw [show A10K2.u7859 = KTree.node A10K2.t7868 (nat_lit 130809222) (nat_lit 16058976194) (nat_lit 0) A10K2.t7869 from rfl, allE_node, rows7868, irow7859, rows7869]
  all_goals rfl

theorem atot7859 : totK PA10K2 A10K2.u7859 = [0, 0, 320479959089, 1733623263391, 3628640675363, 3292830194957, 926520000095, 61110126106, 0, 0] := by
  rw [show A10K2.u7859 = KTree.node A10K2.t7868 (nat_lit 130809222) (nat_lit 16058976194) (nat_lit 0) A10K2.t7869 from rfl, totK_node, tot7868, tot7869]
  decide +kernel

theorem arows7860 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7860 = true := by
  rw [show A10K2.u7860 = KTree.node A10K2.t7870 (nat_lit 130887333) (nat_lit 6733110764) (nat_lit 0) A10K2.t7871 from rfl, allE_node, rows7870, irow7860, rows7871]
  all_goals rfl

theorem atot7860 : totK PA10K2 A10K2.u7860 = [0, 0, 528909646457, 2503039208844, 3923723228727, 2226665722158, 429177153682, 25734533292, 0, 0] := by
  rw [show A10K2.u7860 = KTree.node A10K2.t7870 (nat_lit 130887333) (nat_lit 6733110764) (nat_lit 0) A10K2.t7871 from rfl, totK_node, tot7870, tot7871]
  decide +kernel

theorem arows7866 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7866 = true := by
  rw [show A10K2.u7866 = KTree.node A10K2.t7872 (nat_lit 130893246) (nat_lit 15781906481) (nat_lit 0) A10K2.t7873 from rfl, allE_node, rows7872, irow7866, rows7873]
  all_goals rfl

theorem atot7866 : totK PA10K2 A10K2.u7866 = [0, 0, 584970815629, 2749835007250, 3975599483473, 1907191289145, 252638721342, 6034215561, 0, 0] := by
  rw [show A10K2.u7866 = KTree.node A10K2.t7872 (nat_lit 130893246) (nat_lit 15781906481) (nat_lit 0) A10K2.t7873 from rfl, totK_node, tot7872, tot7873]
  decide +kernel

theorem arows7867 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7867 = true := by
  rw [show A10K2.u7867 = KTree.node A10K2.t7874 (nat_lit 130901176) (nat_lit 10062782981) (nat_lit 0) A10K2.t7875 from rfl, allE_node, rows7874, irow7867, rows7875]
  all_goals rfl

theorem atot7867 : totK PA10K2 A10K2.u7867 = [0, 0, 801848663679, 3115213942768, 4008678085552, 1724098547070, 208775413319, 6239673734, 0, 0] := by
  rw [show A10K2.u7867 = KTree.node A10K2.t7874 (nat_lit 130901176) (nat_lit 10062782981) (nat_lit 0) A10K2.t7875 from rfl, totK_node, tot7874, tot7875]
  decide +kernel

theorem arows7869 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7869 = true := by
  rw [show A10K2.u7869 = KTree.node A10K2.t7876 (nat_lit 130905993) (nat_lit 2625555555) (nat_lit 0) A10K2.t7877 from rfl, allE_node, rows7876, irow7869, rows7877]
  all_goals rfl

theorem atot7869 : totK PA10K2 A10K2.u7869 = [0, 0, 0, 1298964693275, 4211192980015, 3683434093100, 858312784879, 41062513076, 0, 0] := by
  rw [show A10K2.u7869 = KTree.node A10K2.t7876 (nat_lit 130905993) (nat_lit 2625555555) (nat_lit 0) A10K2.t7877 from rfl, totK_node, tot7876, tot7877]
  decide +kernel

theorem arows7870 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7870 = true := by
  rw [show A10K2.u7870 = KTree.node A10K2.t7878 (nat_lit 130919830) (nat_lit 15972102701) (nat_lit 0) A10K2.t7879 from rfl, allE_node, rows7878, irow7870, rows7879]
  all_goals rfl

theorem atot7870 : totK PA10K2 A10K2.u7870 = [0, 0, 0, 522754546307, 2624000280887, 3963432314886, 1987885668870, 356140713749, 13576218110, 0] := by
  rw [show A10K2.u7870 = KTree.node A10K2.t7878 (nat_lit 130919830) (nat_lit 15972102701) (nat_lit 0) A10K2.t7879 from rfl, totK_node, tot7878, tot7879]
  decide +kernel

theorem arows7873 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7873 = true := by
  rw [show A10K2.u7873 = KTree.node A10K2.t7880 (nat_lit 130926071) (nat_lit 14245400144) (nat_lit 0) A10K2.t7881 from rfl, allE_node, rows7880, irow7873, rows7881]
  all_goals rfl

theorem atot7873 : totK PA10K2 A10K2.u7873 = [0, 0, 0, 578735677257, 2862669011040, 4112227478698, 1729997361442, 169830244043, 0, 0] := by
  rw [show A10K2.u7873 = KTree.node A10K2.t7880 (nat_lit 130926071) (nat_lit 14245400144) (nat_lit 0) A10K2.t7881 from rfl, totK_node, tot7880, tot7881]
  decide +kernel

theorem arows7874 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7874 = true := by
  rw [show A10K2.u7874 = KTree.node A10K2.t7882 (nat_lit 130934685) (nat_lit 4844459924) (nat_lit 0) A10K2.t7883 from rfl, allE_node, rows7882, irow7874, rows7883]
  all_goals rfl

theorem atot7874 : totK PA10K2 A10K2.u7874 = [0, 0, 304922396905, 1675298484329, 3498174964152, 3348145271428, 1102668855728, 80638994390, 0, 0] := by
  rw [show A10K2.u7874 = KTree.node A10K2.t7882 (nat_lit 130934685) (nat_lit 4844459924) (nat_lit 0) A10K2.t7883 from rfl, totK_node, tot7882, tot7883]
  decide +kernel

theorem arows7876 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7876 = true := by
  rw [show A10K2.u7876 = KTree.node A10K2.t7884 (nat_lit 130952895) (nat_lit 13811702522) (nat_lit 0) A10K2.t7885 from rfl, allE_node, rows7884, irow7876, rows7885]
  all_goals rfl

theorem atot7876 : totK PA10K2 A10K2.u7876 = [0, 0, 457327470340, 2441068030849, 4102951865301, 2288357010879, 438817822524, 25734533292, 0, 0] := by
  rw [show A10K2.u7876 = KTree.node A10K2.t7884 (nat_lit 130952895) (nat_lit 13811702522) (nat_lit 0) A10K2.t7885 from rfl, totK_node, tot7884, tot7885]
  decide +kernel

theorem arows7877 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7877 = true := by
  rw [show A10K2.u7877 = KTree.node A10K2.t7886 (nat_lit 130959260) (nat_lit 8892659703) (nat_lit 0) A10K2.t7887 from rfl, allE_node, rows7886, irow7877, rows7887]
  all_goals rfl

theorem atot7877 : totK PA10K2 A10K2.u7877 = [0, 0, 561217355197, 2711258896415, 4138345482816, 2040768394414, 268208933333, 6034215561, 0, 0] := by
  rw [show A10K2.u7877 = KTree.node A10K2.t7886 (nat_lit 130959260) (nat_lit 8892659703) (nat_lit 0) A10K2.t7887 from rfl, totK_node, tot7886, tot7887]
  decide +kernel

theorem arows7881 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7881 = true := by
  rw [show A10K2.u7881 = KTree.node A10K2.t7888 (nat_lit 130984042) (nat_lit 5615785077) (nat_lit 0) A10K2.t7889 from rfl, allE_node, rows7888, irow7881, rows7889]
  all_goals rfl

theorem atot7881 : totK PA10K2 A10K2.u7881 = [0, 0, 0, 1077920317788, 3879921992121, 3776208011663, 903227534772, 45583950843, 0, 0] := by
  rw [show A10K2.u7881 = KTree.node A10K2.t7888 (nat_lit 130984042) (nat_lit 5615785077) (nat_lit 0) A10K2.t7889 from rfl, totK_node, tot7888, tot7889]
  decide +kernel

theorem arows7882 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7882 = true := by
  rw [show A10K2.u7882 = KTree.node A10K2.t7890 (nat_lit 131006789) (nat_lit 6272045178) (nat_lit 0) A10K2.t7891 from rfl, allE_node, rows7890, irow7882, rows7891]
  all_goals rfl

theorem atot7882 : totK PA10K2 A10K2.u7882 = [0, 0, 588716830688, 2511367155427, 3910398863563, 2470230789753, 412590540218, 12260057084, 0, 0] := by
  rw [show A10K2.u7882 = KTree.node A10K2.t7890 (nat_lit 131006789) (nat_lit 6272045178) (nat_lit 0) A10K2.t7891 from rfl, totK_node, tot7890, tot7891]
  decide +kernel

theorem arows7884 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7884 = true := by
  rw [show A10K2.u7884 = KTree.node A10K2.t7892 (nat_lit 131015965) (nat_lit 6271232542) (nat_lit 0) A10K2.t7893 from rfl, allE_node, rows7892, irow7884, rows7893]
  all_goals rfl

theorem atot7884 : totK PA10K2 A10K2.u7884 = [0, 0, 677369765217, 2848774510904, 3998455492972, 2064900369370, 309214294674, 7007974415, 0, 0] := by
  rw [show A10K2.u7884 = KTree.node A10K2.t7892 (nat_lit 131015965) (nat_lit 6271232542) (nat_lit 0) A10K2.t7893 from rfl, totK_node, tot7892, tot7893]
  decide +kernel

theorem arows7885 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7885 = true := by
  rw [show A10K2.u7885 = KTree.node A10K2.t7894 (nat_lit 131020630) (nat_lit 10513239227) (nat_lit 0) A10K2.t7895 from rfl, allE_node, rows7894, irow7885, rows7895]
  all_goals rfl

theorem atot7885 : totK PA10K2 A10K2.u7885 = [0, 0, 371444899111, 2069314359416, 4026657487110, 2869872599937, 561213466814, 18710738642, 0, 0] := by
  rw [show A10K2.u7885 = KTree.node A10K2.t7894 (nat_lit 131020630) (nat_lit 10513239227) (nat_lit 0) A10K2.t7895 from rfl, totK_node, tot7894, tot7895]
  decide +kernel

theorem arows7888 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7888 = true := by
  rw [show A10K2.u7888 = KTree.node A10K2.t7896 (nat_lit 131034331) (nat_lit 9651654716) (nat_lit 0) A10K2.t7897 from rfl, allE_node, rows7896, irow7888, rows7897]
  all_goals rfl

theorem atot7888 : totK PA10K2 A10K2.u7888 = [0, 0, 615112866711, 2835774508563, 4156507734891, 2108804331765, 282651522849, 6281495166, 0, 0] := by
  rw [show A10K2.u7888 = KTree.node A10K2.t7896 (nat_lit 131034331) (nat_lit 9651654716) (nat_lit 0) A10K2.t7897 from rfl, totK_node, tot7896, tot7897]
  decide +kernel

theorem arows7889 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7889 = true := by
  rw [show A10K2.u7889 = KTree.node A10K2.t7898 (nat_lit 131038897) (nat_lit 6351094828) (nat_lit 0) A10K2.t7899 from rfl, allE_node, rows7898, irow7889, rows7899]
  all_goals rfl

theorem atot7889 : totK PA10K2 A10K2.u7889 = [0, 470692968618, 1520597896108, 2010546939334, 2597059158220, 2453387205466, 772425555532, 56100664475, 0, 0] := by
  rw [show A10K2.u7889 = KTree.node A10K2.t7898 (nat_lit 131038897) (nat_lit 6351094828) (nat_lit 0) A10K2.t7899 from rfl, totK_node, tot7898, tot7899]
  decide +kernel

theorem arows7891 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7891 = true := by
  rw [show A10K2.u7891 = KTree.node A10K2.t7900 (nat_lit 131600499) (nat_lit 3377497069) (nat_lit 0) A10K2.t7901 from rfl, allE_node, rows7900, irow7891, rows7901]
  all_goals rfl

theorem atot7891 : totK PA10K2 A10K2.u7891 = [0, 328596557822, 2048000760966, 3903790661871, 2604370602411, 535175618258, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u7891 = KTree.node A10K2.t7900 (nat_lit 131600499) (nat_lit 3377497069) (nat_lit 0) A10K2.t7901 from rfl, totK_node, tot7900, tot7901]
  decide +kernel

theorem arows7892 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7892 = true := by
  rw [show A10K2.u7892 = KTree.node A10K2.t7902 (nat_lit 131615267) (nat_lit 3706207735) (nat_lit 0) A10K2.t7903 from rfl, allE_node, rows7902, irow7892, rows7903]
  all_goals rfl

theorem atot7892 : totK PA10K2 A10K2.u7892 = [0, 732580876681, 3035182022284, 3977667887500, 1722758431055, 172158936560, 0, 0, 0, 0] := by
  rw [show A10K2.u7892 = KTree.node A10K2.t7902 (nat_lit 131615267) (nat_lit 3706207735) (nat_lit 0) A10K2.t7903 from rfl, totK_node, tot7902, tot7903]
  decide +kernel

theorem arows7897 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7897 = true := by
  rw [show A10K2.u7897 = KTree.node A10K2.t7904 (nat_lit 131624438) (nat_lit 16892777961) (nat_lit 0) A10K2.t7905 from rfl, allE_node, rows7904, irow7897, rows7905]
  all_goals rfl

theorem atot7897 : totK PA10K2 A10K2.u7897 = [0, 540969523310, 2637023841829, 4250318535353, 2354204574557, 358696044816, 6853348008, 0, 0, 0] := by
  rw [show A10K2.u7897 = KTree.node A10K2.t7904 (nat_lit 131624438) (nat_lit 16892777961) (nat_lit 0) A10K2.t7905 from rfl, totK_node, tot7904, tot7905]
  decide +kernel

theorem arows7898 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7898 = true := by
  rw [show A10K2.u7898 = KTree.node A10K2.t7906 (nat_lit 131629089) (nat_lit 10204605750) (nat_lit 0) A10K2.t7907 from rfl, allE_node, rows7906, irow7898, rows7907]
  all_goals rfl

theorem atot7898 : totK PA10K2 A10K2.u7898 = [0, 0, 943925723767, 3567388415808, 4008722482196, 1202594108164, 81793495066, 0, 0, 0] := by
  rw [show A10K2.u7898 = KTree.node A10K2.t7906 (nat_lit 131629089) (nat_lit 10204605750) (nat_lit 0) A10K2.t7907 from rfl, totK_node, tot7906, tot7907]
  decide +kernel

theorem arows7900 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7900 = true := by
  rw [show A10K2.u7900 = KTree.node A10K2.t7908 (nat_lit 131633721) (nat_lit 7115393801) (nat_lit 0) A10K2.t7909 from rfl, allE_node, rows7908, irow7900, rows7909]
  all_goals rfl

theorem atot7900 : totK PA10K2 A10K2.u7900 = [0, 0, 422487972649, 2187189116484, 3870952089069, 2551611164705, 494313873630, 18459763130, 0, 0] := by
  rw [show A10K2.u7900 = KTree.node A10K2.t7908 (nat_lit 131633721) (nat_lit 7115393801) (nat_lit 0) A10K2.t7909 from rfl, totK_node, tot7908, tot7909]
  decide +kernel

theorem arows7901 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7901 = true := by
  rw [show A10K2.u7901 = KTree.node A10K2.t7910 (nat_lit 131649992) (nat_lit 13692855553) (nat_lit 0) A10K2.t7911 from rfl, allE_node, rows7910, irow7901, rows7911]
  all_goals rfl

theorem atot7901 : totK PA10K2 A10K2.u7901 = [0, 0, 750337609834, 3141680234564, 3987626190110, 1527357022829, 146081885813, 0, 0, 0] := by
  rw [show A10K2.u7901 = KTree.node A10K2.t7910 (nat_lit 131649992) (nat_lit 13692855553) (nat_lit 0) A10K2.t7911 from rfl, totK_node, tot7910, tot7911]
  decide +kernel

theorem arows7904 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7904 = true := by
  rw [show A10K2.u7904 = KTree.node A10K2.t7912 (nat_lit 131671222) (nat_lit 15868355175) (nat_lit 0) A10K2.t7913 from rfl, allE_node, rows7912, irow7904, rows7913]
  all_goals rfl

theorem atot7904 : totK PA10K2 A10K2.u7904 = [0, 513260446086, 2241882223889, 3591194211082, 2641427556499, 798187442494, 57551169768, 0, 0, 0] := by
  rw [show A10K2.u7904 = KTree.node A10K2.t7912 (nat_lit 131671222) (nat_lit 15868355175) (nat_lit 0) A10K2.t7913 from rfl, totK_node, tot7912, tot7913]
  decide +kernel

theorem arows7905 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7905 = true := by
  rw [show A10K2.u7905 = KTree.node A10K2.t7914 (nat_lit 131675805) (nat_lit 6046836514) (nat_lit 0) A10K2.t7915 from rfl, allE_node, rows7914, irow7905, rows7915]
  all_goals rfl

theorem atot7905 : totK PA10K2 A10K2.u7905 = [0, 325587018261, 1964932136196, 3985102341346, 2936256378704, 605564732993, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u7905 = KTree.node A10K2.t7914 (nat_lit 131675805) (nat_lit 6046836514) (nat_lit 0) A10K2.t7915 from rfl, totK_node, tot7914, tot7915]
  decide +kernel

theorem arows7907 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7907 = true := by
  rw [show A10K2.u7907 = KTree.node A10K2.t7916 (nat_lit 131683611) (nat_lit 10017670862) (nat_lit 0) A10K2.t7917 from rfl, allE_node, rows7916, irow7907, rows7917]
  all_goals rfl

theorem atot7907 : totK PA10K2 A10K2.u7907 = [0, 775213281328, 3180683900169, 4049337539923, 1611041578834, 148228760919, 0, 0, 0, 0] := by
  rw [show A10K2.u7907 = KTree.node A10K2.t7916 (nat_lit 131683611) (nat_lit 10017670862) (nat_lit 0) A10K2.t7917 from rfl, totK_node, tot7916, tot7917]
  decide +kernel

theorem arows7908 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7908 = true := by
  rw [show A10K2.u7908 = KTree.node A10K2.t7918 (nat_lit 131690375) (nat_lit 14658428996) (nat_lit 0) A10K2.t7919 from rfl, allE_node, rows7918, irow7908, rows7919]
  all_goals rfl

theorem atot7908 : totK PA10K2 A10K2.u7908 = [0, 459706590608, 2401062050732, 4149841103780, 2653280106222, 498074355432, 13814447077, 0, 0, 0] := by
  rw [show A10K2.u7908 = KTree.node A10K2.t7918 (nat_lit 131690375) (nat_lit 14658428996) (nat_lit 0) A10K2.t7919 from rfl, totK_node, tot7918, tot7919]
  decide +kernel

theorem arows7912 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7912 = true := by
  rw [show A10K2.u7912 = KTree.node A10K2.t7920 (nat_lit 131704219) (nat_lit 9868030166) (nat_lit 0) A10K2.t7921 from rfl, allE_node, rows7920, irow7912, rows7921]
  all_goals rfl

theorem atot7912 : totK PA10K2 A10K2.u7912 = [0, 0, 1062032730816, 3709473344241, 3814359417918, 1127591300096, 81687574006, 0, 0, 0] := by
  rw [show A10K2.u7912 = KTree.node A10K2.t7920 (nat_lit 131704219) (nat_lit 9868030166) (nat_lit 0) A10K2.t7921 from rfl, totK_node, tot7920, tot7921]
  decide +kernel

theorem arows7913 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7913 = true := by
  rw [show A10K2.u7913 = KTree.node A10K2.t7922 (nat_lit 131708850) (nat_lit 14791393585) (nat_lit 0) A10K2.t7923 from rfl, allE_node, rows7922, irow7913, rows7923]
  all_goals rfl

theorem atot7913 : totK PA10K2 A10K2.u7913 = [0, 0, 333005825315, 2091828451315, 3965402263897, 2657438444624, 510689365774, 18713227901, 0, 0] := by
  rw [show A10K2.u7913 = KTree.node A10K2.t7922 (nat_lit 131708850) (nat_lit 14791393585) (nat_lit 0) A10K2.t7923 from rfl, totK_node, tot7922, tot7923]
  decide +kernel

theorem arows7915 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7915 = true := by
  rw [show A10K2.u7915 = KTree.node A10K2.t7924 (nat_lit 131717420) (nat_lit 13552313479) (nat_lit 0) A10K2.t7925 from rfl, allE_node, rows7924, irow7915, rows7925]
  all_goals rfl

theorem atot7915 : totK PA10K2 A10K2.u7915 = [0, 0, 681863370816, 3031822628417, 4174941274043, 1711817437334, 153703566953, 0, 0, 0] := by
  rw [show A10K2.u7915 = KTree.node A10K2.t7924 (nat_lit 131717420) (nat_lit 13552313479) (nat_lit 0) A10K2.t7925 from rfl, totK_node, tot7924, tot7925]
  decide +kernel

theorem arows7916 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7916 = true := by
  rw [show A10K2.u7916 = KTree.node A10K2.t7926 (nat_lit 131793223) (nat_lit 6137432837) (nat_lit 0) A10K2.t7927 from rfl, allE_node, rows7926, irow7916, rows7927]
  all_goals rfl

theorem atot7916 : totK PA10K2 A10K2.u7916 = [0, 762038499923, 2727535560094, 3416570454572, 2226187941396, 711981063882, 54060517173, 0, 0, 0] := by
  rw [show A10K2.u7916 = KTree.node A10K2.t7926 (nat_lit 131793223) (nat_lit 6137432837) (nat_lit 0) A10K2.t7927 from rfl, totK_node, tot7926, tot7927]
  decide +kernel

theorem arows7919 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7919 = true := by
  rw [show A10K2.u7919 = KTree.node A10K2.t7928 (nat_lit 131799053) (nat_lit 5716078996) (nat_lit 0) A10K2.t7929 from rfl, allE_node, rows7928, irow7919, rows7929]
  all_goals rfl

theorem atot7919 : totK PA10K2 A10K2.u7919 = [0, 298738363490, 2060090583121, 4096998829753, 2755203960418, 542123803084, 23468087784, 0, 0, 0] := by
  rw [show A10K2.u7919 = KTree.node A10K2.t7928 (nat_lit 131799053) (nat_lit 5716078996) (nat_lit 0) A10K2.t7929 from rfl, totK_node, tot7928, tot7929]
  decide +kernel

theorem arows7920 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7920 = true := by
  rw [show A10K2.u7920 = KTree.node A10K2.t7930 (nat_lit 131804882) (nat_lit 15347524877) (nat_lit 0) A10K2.t7931 from rfl, allE_node, rows7930, irow7920, rows7931]
  all_goals rfl

theorem atot7920 : totK PA10K2 A10K2.u7920 = [0, 467024804561, 2357518466675, 4033417152989, 2447619372483, 449920999308, 23778073807, 0, 0, 0] := by
  rw [show A10K2.u7920 = KTree.node A10K2.t7930 (nat_lit 131804882) (nat_lit 15347524877) (nat_lit 0) A10K2.t7931 from rfl, totK_node, tot7930, tot7931]
  decide +kernel

theorem arows7922 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7922 = true := by
  rw [show A10K2.u7922 = KTree.node A10K2.t7932 (nat_lit 131818657) (nat_lit 1828387628) (nat_lit 0) A10K2.t7933 from rfl, allE_node, rows7932, irow7922, rows7933]
  all_goals rfl

theorem atot7922 : totK PA10K2 A10K2.u7922 = [0, 896434737838, 3377326020303, 3979667255536, 1603380560047, 187506136706, 0, 0, 0, 0] := by
  rw [show A10K2.u7922 = KTree.node A10K2.t7932 (nat_lit 131818657) (nat_lit 1828387628) (nat_lit 0) A10K2.t7933 from rfl, totK_node, tot7932, tot7933]
  decide +kernel

theorem arows7923 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7923 = true := by
  rw [show A10K2.u7923 = KTree.node A10K2.t7934 (nat_lit 131822999) (nat_lit 14384969889) (nat_lit 0) A10K2.t7935 from rfl, allE_node, rows7934, irow7923, rows7935]
  all_goals rfl

theorem atot7923 : totK PA10K2 A10K2.u7923 = [0, 0, 1147459774307, 3919753999974, 3889597706884, 1060655745879, 62996513375, 0, 0, 0] := by
  rw [show A10K2.u7923 = KTree.node A10K2.t7934 (nat_lit 131822999) (nat_lit 14384969889) (nat_lit 0) A10K2.t7935 from rfl, totK_node, tot7934, tot7935]
  decide +kernel

theorem arows7931 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7931 = true := by
  rw [show A10K2.u7931 = KTree.node A10K2.t7936 (nat_lit 131828845) (nat_lit 4796924444) (nat_lit 0) A10K2.t7937 from rfl, allE_node, rows7936, irow7931, rows7937]
  all_goals rfl

theorem atot7931 : totK PA10K2 A10K2.u7931 = [0, 0, 733267081194, 3064753117024, 3960379874082, 1752819640647, 231864533094, 6904928264, 0, 0] := by
  rw [show A10K2.u7931 = KTree.node A10K2.t7936 (nat_lit 131828845) (nat_lit 4796924444) (nat_lit 0) A10K2.t7937 from rfl, totK_node, tot7936, tot7937]
  decide +kernel

theorem arows7932 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7932 = true := by
  rw [show A10K2.u7932 = KTree.node A10K2.t7938 (nat_lit 131835577) (nat_lit 2774691345) (nat_lit 0) A10K2.t7939 from rfl, allE_node, rows7938, irow7932, rows7939]
  all_goals rfl

theorem atot7932 : totK PA10K2 A10K2.u7932 = [0, 0, 764753336025, 3151716768781, 4102728369399, 1672899625941, 138679465296, 0, 0, 0] := by
  rw [show A10K2.u7932 = KTree.node A10K2.t7938 (nat_lit 131835577) (nat_lit 2774691345) (nat_lit 0) A10K2.t7939 from rfl, totK_node, tot7938, tot7939]
  decide +kernel

theorem arows7934 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7934 = true := by
  rw [show A10K2.u7934 = KTree.node A10K2.t7940 (nat_lit 131841245) (nat_lit 3201885653) (nat_lit 0) A10K2.t7941 from rfl, allE_node, rows7940, irow7934, rows7941]
  all_goals rfl

theorem atot7934 : totK PA10K2 A10K2.u7934 = [0, 0, 563781224979, 2624070908150, 4061310828554, 2309285668184, 329636622658, 7047025452, 0, 0] := by
  rw [show A10K2.u7934 = KTree.node A10K2.t7940 (nat_lit 131841245) (nat_lit 3201885653) (nat_lit 0) A10K2.t7941 from rfl, totK_node, tot7940, tot7941]
  decide +kernel

theorem arows7935 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7935 = true := by
  rw [show A10K2.u7935 = KTree.node A10K2.t7942 (nat_lit 131854343) (nat_lit 13841851386) (nat_lit 0) A10K2.t7943 from rfl, allE_node, rows7942, irow7935, rows7943]
  all_goals rfl

theorem atot7935 : totK PA10K2 A10K2.u7935 = [0, 0, 331364255318, 2148900466990, 4222569541557, 2785312750231, 458647460984, 12224107035, 0, 0] := by
  rw [show A10K2.u7935 = KTree.node A10K2.t7942 (nat_lit 131854343) (nat_lit 13841851386) (nat_lit 0) A10K2.t7943 from rfl, totK_node, tot7942, tot7943]
  decide +kernel

theorem arows7938 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7938 = true := by
  rw [show A10K2.u7938 = KTree.node A10K2.t7944 (nat_lit 131858930) (nat_lit 11539759144) (nat_lit 0) A10K2.t7945 from rfl, allE_node, rows7944, irow7938, rows7945]
  all_goals rfl

theorem atot7938 : totK PA10K2 A10K2.u7938 = [0, 0, 806920830838, 2903762564358, 3477902485923, 1871825108100, 548127426290, 48886019071, 0, 0] := by
  rw [show A10K2.u7938 = KTree.node A10K2.t7944 (nat_lit 131858930) (nat_lit 11539759144) (nat_lit 0) A10K2.t7945 from rfl, totK_node, tot7944, tot7945]
  decide +kernel

theorem arows7939 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7939 = true := by
  rw [show A10K2.u7939 = KTree.node A10K2.t7946 (nat_lit 131864633) (nat_lit 7217153059) (nat_lit 0) A10K2.t7947 from rfl, allE_node, rows7946, irow7939, rows7947]
  all_goals rfl

theorem atot7939 : totK PA10K2 A10K2.u7939 = [0, 0, 271056309428, 1906810877871, 4012939928687, 2862573850487, 539976102423, 18469913835, 0, 0] := by
  rw [show A10K2.u7939 = KTree.node A10K2.t7946 (nat_lit 131864633) (nat_lit 7217153059) (nat_lit 0) A10K2.t7947 from rfl, totK_node, tot7946, tot7947]
  decide +kernel

theorem arows7941 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7941 = true := by
  rw [show A10K2.u7941 = KTree.node A10K2.t7948 (nat_lit 131881479) (nat_lit 8427346911) (nat_lit 0) A10K2.t7949 from rfl, allE_node, rows7948, irow7941, rows7949]
  all_goals rfl

theorem atot7941 : totK PA10K2 A10K2.u7941 = [0, 0, 680080675331, 3009948832907, 4157533211892, 1671266455822, 153524644231, 0, 0, 0] := by
  rw [show A10K2.u7941 = KTree.node A10K2.t7948 (nat_lit 131881479) (nat_lit 8427346911) (nat_lit 0) A10K2.t7949 from rfl, totK_node, tot7948, tot7949]
  decide +kernel

theorem arows7942 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7942 = true := by
  rw [show A10K2.u7942 = KTree.node A10K2.t7950 (nat_lit 131887511) (nat_lit 14377241435) (nat_lit 0) A10K2.t7951 from rfl, allE_node, rows7950, irow7942, rows7951]
  all_goals rfl

theorem atot7942 : totK PA10K2 A10K2.u7942 = [0, 0, 320910162593, 2121983027533, 4284545081841, 3002168738040, 524531266807, 13229391832, 0, 0] := by
  rw [show A10K2.u7942 = KTree.node A10K2.t7950 (nat_lit 131887511) (nat_lit 14377241435) (nat_lit 0) A10K2.t7951 from rfl, totK_node, tot7950, tot7951]
  decide +kernel

theorem arows7946 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7946 = true := by
  rw [show A10K2.u7946 = KTree.node A10K2.t7952 (nat_lit 131892154) (nat_lit 11203242620) (nat_lit 0) A10K2.t7953 from rfl, allE_node, rows7952, irow7946, rows7953]
  all_goals rfl

theorem atot7946 : totK PA10K2 A10K2.u7946 = [0, 0, 0, 805785007192, 3360218840568, 4093328178549, 1375855213018, 96715438682, 0, 0] := by
  rw [show A10K2.u7946 = KTree.node A10K2.t7952 (nat_lit 131892154) (nat_lit 11203242620) (nat_lit 0) A10K2.t7953 from rfl, totK_node, tot7952, tot7953]
  decide +kernel

theorem arows7947 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7947 = true := by
  rw [show A10K2.u7947 = KTree.node A10K2.t7954 (nat_lit 131898879) (nat_lit 10024016499) (nat_lit 0) A10K2.t7955 from rfl, allE_node, rows7954, irow7947, rows7955]
  all_goals rfl

theorem atot7947 : totK PA10K2 A10K2.u7947 = [0, 0, 0, 669685353181, 2868041212076, 3884451813591, 1717075955158, 237558249018, 7007974415, 0] := by
  rw [show A10K2.u7947 = KTree.node A10K2.t7954 (nat_lit 131898879) (nat_lit 10024016499) (nat_lit 0) A10K2.t7955 from rfl, totK_node, tot7954, tot7955]
  decide +kernel

theorem arows7949 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7949 = true := by
  rw [show A10K2.u7949 = KTree.node A10K2.t7956 (nat_lit 131919301) (nat_lit 3574340679) (nat_lit 0) A10K2.t7957 from rfl, allE_node, rows7956, irow7949, rows7957]
  all_goals rfl

theorem atot7949 : totK PA10K2 A10K2.u7949 = [0, 0, 312139800791, 1698420900785, 3605912312013, 3395913907480, 1027844685202, 68789595223, 0, 0] := by
  rw [show A10K2.u7949 = KTree.node A10K2.t7956 (nat_lit 131919301) (nat_lit 3574340679) (nat_lit 0) A10K2.t7957 from rfl, totK_node, tot7956, tot7957]
  decide +kernel

theorem arows7950 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7950 = true := by
  rw [show A10K2.u7950 = KTree.node A10K2.t7958 (nat_lit 131936190) (nat_lit 16355011105) (nat_lit 0) A10K2.t7959 from rfl, allE_node, rows7958, irow7950, rows7959]
  all_goals rfl

theorem atot7950 : totK PA10K2 A10K2.u7950 = [0, 0, 498402015416, 2384558700152, 3914540317179, 2371744878234, 450450795527, 18722998264, 0, 0] := by
  rw [show A10K2.u7950 = KTree.node A10K2.t7958 (nat_lit 131936190) (nat_lit 16355011105) (nat_lit 0) A10K2.t7959 from rfl, totK_node, tot7958, tot7959]
  decide +kernel

theorem arows7953 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7953 = true := by
  rw [show A10K2.u7953 = KTree.node A10K2.t7960 (nat_lit 131942561) (nat_lit 3579350703) (nat_lit 0) A10K2.t7961 from rfl, allE_node, rows7960, irow7953, rows7961]
  all_goals rfl

theorem atot7953 : totK PA10K2 A10K2.u7953 = [0, 0, 617511295248, 2740968529142, 4033406698134, 2042729564875, 238562804598, 0, 0, 0] := by
  rw [show A10K2.u7953 = KTree.node A10K2.t7960 (nat_lit 131942561) (nat_lit 3579350703) (nat_lit 0) A10K2.t7961 from rfl, totK_node, tot7960, tot7961]
  decide +kernel

theorem arows7954 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7954 = true := by
  rw [show A10K2.u7954 = KTree.node A10K2.t7962 (nat_lit 131951801) (nat_lit 5947340225) (nat_lit 0) A10K2.t7963 from rfl, allE_node, rows7962, irow7954, rows7963]
  all_goals rfl

theorem atot7954 : totK PA10K2 A10K2.u7954 = [0, 0, 658300742239, 2993100046897, 4268330109553, 2062744381958, 282685939260, 6279851884, 0, 0] := by
  rw [show A10K2.u7954 = KTree.node A10K2.t7962 (nat_lit 131951801) (nat_lit 5947340225) (nat_lit 0) A10K2.t7963 from rfl, totK_node, tot7962, tot7963]
  decide +kernel

theorem arows7956 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7956 = true := by
  rw [show A10K2.u7956 = KTree.node A10K2.t7964 (nat_lit 131956608) (nat_lit 14373089450) (nat_lit 0) A10K2.t7965 from rfl, allE_node, rows7964, irow7956, rows7965]
  all_goals rfl

theorem atot7956 : totK PA10K2 A10K2.u7956 = [0, 0, 0, 1011513169035, 3697825574651, 3879733787122, 1168894643460, 74967760232, 0, 0] := by
  rw [show A10K2.u7956 = KTree.node A10K2.t7964 (nat_lit 131956608) (nat_lit 14373089450) (nat_lit 0) A10K2.t7965 from rfl, totK_node, tot7964, tot7965]
  decide +kernel

theorem arows7957 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7957 = true := by
  rw [show A10K2.u7957 = KTree.node A10K2.t7966 (nat_lit 131970452) (nat_lit 9060286071) (nat_lit 0) A10K2.t7967 from rfl, allE_node, rows7966, irow7957, rows7967]
  all_goals rfl

theorem atot7957 : totK PA10K2 A10K2.u7957 = [0, 0, 0, 526816161710, 2631101402312, 4188647543366, 2095966175527, 274285540872, 7151180950, 0] := by
  rw [show A10K2.u7957 = KTree.node A10K2.t7966 (nat_lit 131970452) (nat_lit 9060286071) (nat_lit 0) A10K2.t7967 from rfl, totK_node, tot7966, tot7967]
  decide +kernel

theorem arows7962 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7962 = true := by
  rw [show A10K2.u7962 = KTree.node A10K2.t7968 (nat_lit 131982782) (nat_lit 16292101936) (nat_lit 0) A10K2.t7969 from rfl, allE_node, rows7968, irow7962, rows7969]
  all_goals rfl

theorem atot7962 : totK PA10K2 A10K2.u7962 = [0, 0, 0, 1031085417209, 3801782223490, 4016177638619, 1154089642105, 54978839469, 0, 0] := by
  rw [show A10K2.u7962 = KTree.node A10K2.t7968 (nat_lit 131982782) (nat_lit 16292101936) (nat_lit 0) A10K2.t7969 from rfl, totK_node, tot7968, tot7969]
  decide +kernel

theorem arows7963 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7963 = true := by
  rw [show A10K2.u7963 = KTree.node A10K2.t7970 (nat_lit 132058260) (nat_lit 7403840729) (nat_lit 0) A10K2.t7971 from rfl, allE_node, rows7970, irow7963, rows7971]
  all_goals rfl

theorem atot7963 : totK PA10K2 A10K2.u7963 = [0, 0, 761537111178, 3086011902902, 3933179270584, 1715736560159, 274933457148, 11991740650, 0, 0] := by
  rw [show A10K2.u7963 = KTree.node A10K2.t7970 (nat_lit 132058260) (nat_lit 7403840729) (nat_lit 0) A10K2.t7971 from rfl, totK_node, tot7970, tot7971]
  decide +kernel

theorem arows7965 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7965 = true := by
  rw [show A10K2.u7965 = KTree.node A10K2.t7972 (nat_lit 132064702) (nat_lit 16085329573) (nat_lit 0) A10K2.t7973 from rfl, allE_node, rows7972, irow7965, rows7973]
  all_goals rfl

theorem atot7965 : totK PA10K2 A10K2.u7965 = [0, 0, 765263111575, 3048389046001, 3944953736107, 1837452858488, 215504006151, 0, 0, 0] := by
  rw [show A10K2.u7965 = KTree.node A10K2.t7972 (nat_lit 132064702) (nat_lit 16085329573) (nat_lit 0) A10K2.t7973 from rfl, totK_node, tot7972, tot7973]
  decide +kernel

theorem arows7966 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7966 = true := by
  rw [show A10K2.u7966 = KTree.node A10K2.t7974 (nat_lit 132069668) (nat_lit 9399913446) (nat_lit 0) A10K2.t7975 from rfl, allE_node, rows7974, irow7966, rows7975]
  all_goals rfl

theorem atot7966 : totK PA10K2 A10K2.u7966 = [0, 0, 280714159330, 2002034390697, 4185119908135, 2882789548786, 469825237700, 12219140272, 0, 0] := by
  rw [show A10K2.u7966 = KTree.node A10K2.t7974 (nat_lit 132069668) (nat_lit 9399913446) (nat_lit 0) A10K2.t7975 from rfl, totK_node, tot7974, tot7975]
  decide +kernel

theorem arows7969 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7969 = true := by
  rw [show A10K2.u7969 = KTree.node A10K2.t7976 (nat_lit 132083258) (nat_lit 11499283544) (nat_lit 0) A10K2.t7977 from rfl, allE_node, rows7976, irow7969, rows7977]
  all_goals rfl

theorem atot7969 : totK PA10K2 A10K2.u7969 = [0, 0, 613737279027, 2718796933908, 4108762125865, 2231410870604, 303813872238, 6772895877, 0, 0] := by
  rw [show A10K2.u7969 = KTree.node A10K2.t7976 (nat_lit 132083258) (nat_lit 11499283544) (nat_lit 0) A10K2.t7977 from rfl, totK_node, tot7976, tot7977]
  decide +kernel

theorem arows7970 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7970 = true := by
  rw [show A10K2.u7970 = KTree.node A10K2.t7978 (nat_lit 132087799) (nat_lit 14899910164) (nat_lit 0) A10K2.t7979 from rfl, allE_node, rows7978, irow7970, rows7979]
  all_goals rfl

theorem atot7970 : totK PA10K2 A10K2.u7970 = [0, 0, 0, 1068383952832, 3755706269837, 3922439087516, 1116210836460, 68058142506, 0, 0] := by
  rw [show A10K2.u7970 = KTree.node A10K2.t7978 (nat_lit 132087799) (nat_lit 14899910164) (nat_lit 0) A10K2.t7979 from rfl, totK_node, tot7978, tot7979]
  decide +kernel

theorem arows7972 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7972 = true := by
  rw [show A10K2.u7972 = KTree.node A10K2.t7980 (nat_lit 132092855) (nat_lit 14765989163) (nat_lit 0) A10K2.t7981 from rfl, allE_node, rows7980, irow7972, rows7981]
  all_goals rfl

theorem atot7972 : totK PA10K2 A10K2.u7972 = [0, 0, 0, 416659205951, 2467340160569, 4310592893545, 2283475429743, 284871461903, 6318667960, 0] := by
  rw [show A10K2.u7972 = KTree.node A10K2.t7980 (nat_lit 132092855) (nat_lit 14765989163) (nat_lit 0) A10K2.t7981 from rfl, totK_node, tot7980, tot7981]
  decide +kernel

theorem arows7973 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7973 = true := by
  rw [show A10K2.u7973 = KTree.node A10K2.t7982 (nat_lit 132101299) (nat_lit 10369284172) (nat_lit 0) A10K2.t7983 from rfl, allE_node, rows7982, irow7973, rows7983]
  all_goals rfl

theorem atot7973 : totK PA10K2 A10K2.u7973 = [0, 0, 0, 586845908123, 2770375013222, 4140818829097, 2131888799664, 277152403198, 6439430839, 0] := by
  rw [show A10K2.u7973 = KTree.node A10K2.t7982 (nat_lit 132101299) (nat_lit 10369284172) (nat_lit 0) A10K2.t7983 from rfl, totK_node, tot7982, tot7983]
  decide +kernel

theorem arows7977 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7977 = true := by
  rw [show A10K2.u7977 = KTree.node A10K2.t7984 (nat_lit 132115512) (nat_lit 14679186370) (nat_lit 0) A10K2.t7985 from rfl, allE_node, rows7984, irow7977, rows7985]
  all_goals rfl

theorem atot7977 : totK PA10K2 A10K2.u7977 = [0, 0, 0, 755595348039, 3220148014653, 4144474328888, 1626936146091, 134020138859, 0, 0] := by
  rw [show A10K2.u7977 = KTree.node A10K2.t7984 (nat_lit 132115512) (nat_lit 14679186370) (nat_lit 0) A10K2.t7985 from rfl, totK_node, tot7984, tot7985]
  decide +kernel

theorem arows7978 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7978 = true := by
  rw [show A10K2.u7978 = KTree.node A10K2.t7986 (nat_lit 132120069) (nat_lit 3677731553) (nat_lit 0) A10K2.t7987 from rfl, allE_node, rows7986, irow7978, rows7987]
  all_goals rfl

theorem atot7978 : totK PA10K2 A10K2.u7978 = [0, 0, 396273731552, 1250093511923, 1870539990595, 2701591767062, 2679932623890, 849277833310, 61018386929, 0] := by
  rw [show A10K2.u7978 = KTree.node A10K2.t7986 (nat_lit 132120069) (nat_lit 3677731553) (nat_lit 0) A10K2.t7987 from rfl, totK_node, tot7986, tot7987]
  decide +kernel

theorem arows7980 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7980 = true := by
  rw [show A10K2.u7980 = KTree.node A10K2.t7988 (nat_lit 132124608) (nat_lit 14718895254) (nat_lit 0) A10K2.t7989 from rfl, allE_node, rows7988, irow7980, rows7989]
  all_goals rfl

theorem atot7980 : totK PA10K2 A10K2.u7980 = [0, 0, 450701360862, 2381115107507, 3928525835073, 2284068778521, 444169673177, 25371180993, 0, 0] := by
  rw [show A10K2.u7980 = KTree.node A10K2.t7988 (nat_lit 132124608) (nat_lit 14718895254) (nat_lit 0) A10K2.t7989 from rfl, totK_node, tot7988, tot7989]
  decide +kernel

theorem arows7981 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7981 = true := by
  rw [show A10K2.u7981 = KTree.node A10K2.t7990 (nat_lit 132137837) (nat_lit 5420028275) (nat_lit 0) A10K2.t7991 from rfl, allE_node, rows7990, irow7981, rows7991]
  all_goals rfl

theorem atot7981 : totK PA10K2 A10K2.u7981 = [0, 0, 582473627888, 2796727324504, 4039481527659, 1843065057385, 245476028813, 5460492893, 0, 0] := by
  rw [show A10K2.u7981 = KTree.node A10K2.t7990 (nat_lit 132137837) (nat_lit 5420028275) (nat_lit 0) A10K2.t7991 from rfl, totK_node, tot7990, tot7991]
  decide +kernel

theorem arows7984 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7984 = true := by
  rw [show A10K2.u7984 = KTree.node A10K2.t7992 (nat_lit 132146422) (nat_lit 16070085294) (nat_lit 0) A10K2.t7993 from rfl, allE_node, rows7992, irow7984, rows7993]
  all_goals rfl

theorem atot7984 : totK PA10K2 A10K2.u7984 = [0, 0, 802361088133, 3152122221390, 3989866639251, 1705429540214, 224174000839, 5976421810, 0, 0] := by
  rw [show A10K2.u7984 = KTree.node A10K2.t7992 (nat_lit 132146422) (nat_lit 16070085294) (nat_lit 0) A10K2.t7993 from rfl, totK_node, tot7992, tot7993]
  decide +kernel

theorem arows7985 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7985 = true := by
  rw [show A10K2.u7985 = KTree.node A10K2.t7994 (nat_lit 132152499) (nat_lit 9264094579) (nat_lit 0) A10K2.t7995 from rfl, allE_node, rows7994, irow7985, rows7995]
  all_goals rfl

theorem atot7985 : totK PA10K2 A10K2.u7985 = [0, 0, 0, 1045928462998, 3766965481642, 3976778955564, 1183154934773, 82919386900, 0, 0] := by
  rw [show A10K2.u7985 = KTree.node A10K2.t7994 (nat_lit 132152499) (nat_lit 9264094579) (nat_lit 0) A10K2.t7995 from rfl, totK_node, tot7994, tot7995]
  decide +kernel

theorem arows7987 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7987 = true := by
  rw [show A10K2.u7987 = KTree.node A10K2.t7996 (nat_lit 132156986) (nat_lit 10536620878) (nat_lit 0) A10K2.t7997 from rfl, allE_node, rows7996, irow7987, rows7997]
  all_goals rfl

theorem atot7987 : totK PA10K2 A10K2.u7987 = [0, 0, 0, 526953387664, 2617064721695, 3959074517725, 1994896690839, 348164061486, 13364899180, 0] := by
  rw [show A10K2.u7987 = KTree.node A10K2.t7996 (nat_lit 132156986) (nat_lit 10536620878) (nat_lit 0) A10K2.t7997 from rfl, totK_node, tot7996, tot7997]
  decide +kernel

theorem arows7988 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7988 = true := by
  rw [show A10K2.u7988 = KTree.node A10K2.t7998 (nat_lit 132170630) (nat_lit 15162412658) (nat_lit 0) A10K2.t7999 from rfl, allE_node, rows7998, irow7988, rows7999]
  all_goals rfl

theorem atot7988 : totK PA10K2 A10K2.u7988 = [0, 0, 0, 580304801326, 2814195822959, 4107847194844, 1771543761961, 168947440495, 0, 0] := by
  rw [show A10K2.u7988 = KTree.node A10K2.t7998 (nat_lit 132170630) (nat_lit 15162412658) (nat_lit 0) A10K2.t7999 from rfl, totK_node, tot7998, tot7999]
  decide +kernel

theorem arows7994 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7994 = true := by
  rw [show A10K2.u7994 = KTree.node A10K2.t8000 (nat_lit 132179866) (nat_lit 14323089292) (nat_lit 0) A10K2.t8001 from rfl, allE_node, rows8000, irow7994, rows8001]
  all_goals rfl

theorem atot7994 : totK PA10K2 A10K2.u7994 = [0, 0, 303501126640, 1514155425892, 3391119733866, 3565936400181, 1151415867835, 82073972667, 0, 0] := by
  rw [show A10K2.u7994 = KTree.node A10K2.t8000 (nat_lit 132179866) (nat_lit 14323089292) (nat_lit 0) A10K2.t8001 from rfl, totK_node, tot8000, tot8001]
  decide +kernel

theorem arows7995 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7995 = true := by
  rw [show A10K2.u7995 = KTree.node A10K2.t8002 (nat_lit 132255217) (nat_lit 8621216862) (nat_lit 0) A10K2.t8003 from rfl, allE_node, rows8002, irow7995, rows8003]
  all_goals rfl

theorem atot7995 : totK PA10K2 A10K2.u7995 = [0, 0, 456053228344, 2536998649342, 4149615527073, 2204847589716, 422302075582, 25371180993, 0, 0] := by
  rw [show A10K2.u7995 = KTree.node A10K2.t8002 (nat_lit 132255217) (nat_lit 8621216862) (nat_lit 0) A10K2.t8003 from rfl, totK_node, tot8002, tot8003]
  decide +kernel

theorem arows7997 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7997 = true := by
  rw [show A10K2.u7997 = KTree.node A10K2.t8004 (nat_lit 132268896) (nat_lit 12608668612) (nat_lit 0) A10K2.t8005 from rfl, allE_node, rows8004, irow7997, rows8005]
  all_goals rfl

theorem atot7997 : totK PA10K2 A10K2.u7997 = [0, 0, 556534364705, 2599905644289, 3991439501082, 2112433936462, 339893714607, 15026531739, 0, 0] := by
  rw [show A10K2.u7997 = KTree.node A10K2.t8004 (nat_lit 132268896) (nat_lit 12608668612) (nat_lit 0) A10K2.t8005 from rfl, totK_node, tot8004, tot8005]
  decide +kernel

theorem arows7998 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7998 = true := by
  rw [show A10K2.u7998 = KTree.node A10K2.t8006 (nat_lit 132288407) (nat_lit 14211692097) (nat_lit 0) A10K2.t8007 from rfl, allE_node, rows8006, irow7998, rows8007]
  all_goals rfl

theorem atot7998 : totK PA10K2 A10K2.u7998 = [0, 0, 0, 1008952171807, 3844770567163, 3871254151268, 848707902051, 34259113881, 0, 0] := by
  rw [show A10K2.u7998 = KTree.node A10K2.t8006 (nat_lit 132288407) (nat_lit 14211692097) (nat_lit 0) A10K2.t8007 from rfl, totK_node, tot8006, tot8007]
  decide +kernel

theorem arows8001 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8001 = true := by
  rw [show A10K2.u8001 = KTree.node A10K2.t8008 (nat_lit 132320262) (nat_lit 15264674383) (nat_lit 0) A10K2.t8009 from rfl, allE_node, rows8008, irow8001, rows8009]
  all_goals rfl

theorem atot8001 : totK PA10K2 A10K2.u8001 = [0, 0, 793101032162, 3196392242270, 4031039806323, 1637619717056, 213759537133, 6356241174, 0, 0] := by
  rw [show A10K2.u8001 = KTree.node A10K2.t8008 (nat_lit 132320262) (nat_lit 15264674383) (nat_lit 0) A10K2.t8009 from rfl, totK_node, tot8008, tot8009]
  decide +kernel

theorem arows8002 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8002 = true := by
  rw [show A10K2.u8002 = KTree.node A10K2.t8010 (nat_lit 132326629) (nat_lit 4273273177) (nat_lit 32) A10K2.t8011 from rfl, allE_node, rows8010, irow8002, rows8011]
  all_goals rfl

theorem atot8002 : totK PA10K2 A10K2.u8002 = [0, 0, 590865579489, 2606598363728, 3936817092949, 2299135576419, 459880618518, 18457393337, 0, 0] := by
  rw [show A10K2.u8002 = KTree.node A10K2.t8010 (nat_lit 132326629) (nat_lit 4273273177) (nat_lit 32) A10K2.t8011 from rfl, totK_node, tot8010, tot8011]
  decide +kernel

theorem arows8004 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8004 = true := by
  rw [show A10K2.u8004 = KTree.node A10K2.t8012 (nat_lit 132341804) (nat_lit 10206002622) (nat_lit 0) A10K2.t8013 from rfl, allE_node, rows8012, irow8004, rows8013]
  all_goals rfl

theorem atot8004 : totK PA10K2 A10K2.u8004 = [0, 0, 540757303387, 2576705663913, 4077868448862, 2345158886748, 404851752631, 12681556880, 0, 0] := by
  rw [show A10K2.u8004 = KTree.node A10K2.t8012 (nat_lit 132341804) (nat_lit 10206002622) (nat_lit 0) A10K2.t8013 from rfl, totK_node, tot8012, tot8013]
  decide +kernel

theorem arows8005 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8005 = true := by
  rw [show A10K2.u8005 = KTree.node A10K2.t8014 (nat_lit 132346299) (nat_lit 6404301529) (nat_lit 0) A10K2.t8015 from rfl, allE_node, rows8014, irow8005, rows8015]
  all_goals rfl

theorem atot8005 : totK PA10K2 A10K2.u8005 = [0, 0, 327737319032, 2068361685822, 4142200784659, 2937079028006, 538878317669, 13816090359, 0, 0] := by
  rw [show A10K2.u8005 = KTree.node A10K2.t8014 (nat_lit 132346299) (nat_lit 6404301529) (nat_lit 0) A10K2.t8015 from rfl, totK_node, tot8014, tot8015]
  decide +kernel

theorem arows8009 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8009 = true := by
  rw [show A10K2.u8009 = KTree.node A10K2.t8016 (nat_lit 132350853) (nat_lit 5053446303) (nat_lit 0) A10K2.t8017 from rfl, allE_node, rows8016, irow8009, rows8017]
  all_goals rfl

theorem atot8009 : totK PA10K2 A10K2.u8009 = [0, 0, 0, 838792245815, 3437785445007, 4122382926158, 1413976936417, 86432258708, 0, 0] := by
  rw [show A10K2.u8009 = KTree.node A10K2.t8016 (nat_lit 132350853) (nat_lit 5053446303) (nat_lit 0) A10K2.t8017 from rfl, totK_node, tot8016, tot8017]
  decide +kernel

theorem arows8010 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8010 = true := by
  rw [show A10K2.u8010 = KTree.node A10K2.t8018 (nat_lit 132357561) (nat_lit 7055377947) (nat_lit 0) A10K2.t8019 from rfl, allE_node, rows8018, irow8010, rows8019]
  all_goals rfl

theorem atot8010 : totK PA10K2 A10K2.u8010 = [0, 0, 0, 589830162524, 2724917236437, 4144888247479, 2158595265544, 300979505753, 6904928264, 0] := by
  rw [show A10K2.u8010 = KTree.node A10K2.t8018 (nat_lit 132357561) (nat_lit 7055377947) (nat_lit 0) A10K2.t8019 from rfl, totK_node, tot8018, tot8019]
  decide +kernel

theorem arows8012 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8012 = true := by
  rw [show A10K2.u8012 = KTree.node A10K2.t8020 (nat_lit 132365745) (nat_lit 8417854209) (nat_lit 0) A10K2.t8021 from rfl, allE_node, rows8020, irow8012, rows8021]
  all_goals rfl

theorem atot8012 : totK PA10K2 A10K2.u8012 = [0, 0, 0, 540460088909, 2642180804710, 4200667705135, 2275904814017, 292312556849, 6766355402, 0] := by
  rw [show A10K2.u8012 = KTree.node A10K2.t8020 (nat_lit 132365745) (nat_lit 8417854209) (nat_lit 0) A10K2.t8021 from rfl, totK_node, tot8020, tot8021]
  decide +kernel

theorem arows8013 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8013 = true := by
  rw [show A10K2.u8013 = KTree.node A10K2.t8022 (nat_lit 132378887) (nat_lit 10382197672) (nat_lit 0) A10K2.t8023 from rfl, allE_node, rows8022, irow8013, rows8023]
  all_goals rfl

theorem atot8013 : totK PA10K2 A10K2.u8013 = [0, 0, 0, 327234200007, 2086209516101, 4156383719680, 2808231521397, 466958072238, 12224107035, 0] := by
  rw [show A10K2.u8013 = KTree.node A10K2.t8022 (nat_lit 132378887) (nat_lit 10382197672) (nat_lit 0) A10K2.t8023 from rfl, totK_node, tot8022, tot8023]
  decide +kernel

theorem arows8016 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8016 = true := by
  rw [show A10K2.u8016 = KTree.node A10K2.t8024 (nat_lit 132383489) (nat_lit 10372125357) (nat_lit 0) A10K2.t8025 from rfl, allE_node, rows8024, irow8016, rows8025]
  all_goals rfl

theorem atot8016 : totK PA10K2 A10K2.u8016 = [0, 0, 0, 846975092414, 3020550923507, 3446699207109, 1793747180497, 543506628872, 48886019071, 0] := by
  rw [show A10K2.u8016 = KTree.node A10K2.t8024 (nat_lit 132383489) (nat_lit 10372125357) (nat_lit 0) A10K2.t8025 from rfl, totK_node, tot8024, tot8025]
  decide +kernel

theorem arows8017 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8017 = true := by
  rw [show A10K2.u8017 = KTree.node A10K2.t8026 (nat_lit 132389120) (nat_lit 14397781664) (nat_lit 0) A10K2.t8027 from rfl, allE_node, rows8026, irow8017, rows8027]
  all_goals rfl

theorem atot8017 : totK PA10K2 A10K2.u8017 = [0, 0, 0, 287800902345, 1933168024275, 4122120578093, 2805370942659, 476385545717, 13364899180, 0] := by
  rw [show A10K2.u8017 = KTree.node A10K2.t8026 (nat_lit 132389120) (nat_lit 14397781664) (nat_lit 0) A10K2.t8027 from rfl, totK_node, tot8026, tot8027]
  decide +kernel

theorem arows8019 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8019 = true := by
  rw [show A10K2.u8019 = KTree.node A10K2.t8028 (nat_lit 132405261) (nat_lit 5823242822) (nat_lit 0) A10K2.t8029 from rfl, allE_node, rows8028, irow8019, rows8029]
  all_goals rfl

theorem atot8019 : totK PA10K2 A10K2.u8019 = [0, 0, 0, 783025495308, 3302758229709, 4052894660120, 1350477920898, 86760983835, 0, 0] := by
  rw [show A10K2.u8019 = KTree.node A10K2.t8028 (nat_lit 132405261) (nat_lit 5823242822) (nat_lit 0) A10K2.t8029 from rfl, totK_node, tot8028, tot8029]
  decide +kernel

theorem arows8020 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8020 = true := by
  rw [show A10K2.u8020 = KTree.node A10K2.t8030 (nat_lit 132411681) (nat_lit 9898184941) (nat_lit 0) A10K2.t8031 from rfl, allE_node, rows8030, irow8020, rows8031]
  all_goals rfl

theorem atot8020 : totK PA10K2 A10K2.u8020 = [0, 0, 0, 314008318368, 2158389862516, 4339019766178, 2871677998882, 422132083639, 6853348008, 0] := by
  rw [show A10K2.u8020 = KTree.node A10K2.t8030 (nat_lit 132411681) (nat_lit 9898184941) (nat_lit 0) A10K2.t8031 from rfl, totK_node, tot8030, tot8031]
  decide +kernel

theorem arows8025 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8025 = true := by
  rw [show A10K2.u8025 = KTree.node A10K2.t8032 (nat_lit 132417829) (nat_lit 7473810852) (nat_lit 0) A10K2.t8033 from rfl, allE_node, rows8032, irow8025, rows8033]
  all_goals rfl

theorem atot8025 : totK PA10K2 A10K2.u8025 = [0, 0, 0, 0, 828937084469, 3423714909007, 4008917628007, 1295771820359, 83716129134, 0] := by
  rw [show A10K2.u8025 = KTree.node A10K2.t8032 (nat_lit 132417829) (nat_lit 7473810852) (nat_lit 0) A10K2.t8033 from rfl, totK_node, tot8032, tot8033]
  decide +kernel

theorem arows8026 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8026 = true := by
  rw [show A10K2.u8026 = KTree.node A10K2.t8034 (nat_lit 132432421) (nat_lit 7015064330) (nat_lit 0) A10K2.t8035 from rfl, allE_node, rows8034, irow8026, rows8035]
  all_goals rfl

theorem atot8026 : totK PA10K2 A10K2.u8026 = [0, 0, 0, 0, 948119221386, 3363984582468, 3649349645111, 1441154886117, 211960309184, 7237400819] := by
  rw [show A10K2.u8026 = KTree.node A10K2.t8034 (nat_lit 132432421) (nat_lit 7015064330) (nat_lit 0) A10K2.t8035 from rfl, totK_node, tot8034, tot8035]
  decide +kernel

theorem arows8028 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8028 = true := by
  rw [show A10K2.u8028 = KTree.node A10K2.t8036 (nat_lit 132514244) (nat_lit 9006403316) (nat_lit 0) A10K2.t8037 from rfl, allE_node, rows8036, irow8028, rows8037]
  all_goals rfl

theorem atot8028 : totK PA10K2 A10K2.u8028 = [0, 0, 0, 759378239577, 2971581966445, 3767096361949, 1957500058956, 431872071291, 29010686974, 0] := by
  rw [show A10K2.u8028 = KTree.node A10K2.t8036 (nat_lit 132514244) (nat_lit 9006403316) (nat_lit 0) A10K2.t8037 from rfl, totK_node, tot8036, tot8037]
  decide +kernel

theorem arows8029 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8029 = true := by
  rw [show A10K2.u8029 = KTree.node A10K2.t8038 (nat_lit 132530240) (nat_lit 15398834173) (nat_lit 0) A10K2.t8039 from rfl, allE_node, rows8038, irow8029, rows8039]
  all_goals rfl

theorem atot8029 : totK PA10K2 A10K2.u8029 = [0, 0, 0, 671384611811, 3196963932792, 4203111175692, 1467742059439, 88167045842, 0, 0] := by
  rw [show A10K2.u8029 = KTree.node A10K2.t8038 (nat_lit 132530240) (nat_lit 15398834173) (nat_lit 0) A10K2.t8039 from rfl, totK_node, tot8038, tot8039]
  decide +kernel

theorem arows8032 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8032 = true := by
  rw [show A10K2.u8032 = KTree.node A10K2.t8040 (nat_lit 132582585) (nat_lit 6124308160) (nat_lit 0) A10K2.t8041 from rfl, allE_node, rows8040, irow8032, rows8041]
  all_goals rfl

theorem atot8032 : totK PA10K2 A10K2.u8032 = [0, 0, 0, 677552088158, 2951193001657, 4021600134225, 1838431053080, 273606702136, 12473006693, 0] := by
  rw [show A10K2.u8032 = KTree.node A10K2.t8040 (nat_lit 132582585) (nat_lit 6124308160) (nat_lit 0) A10K2.t8041 from rfl, totK_node, tot8040, tot8041]
  decide +kernel

theorem arows8033 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8033 = true := by
  rw [show A10K2.u8033 = KTree.node A10K2.t8042 (nat_lit 132589282) (nat_lit 13752822675) (nat_lit 0) A10K2.t8043 from rfl, allE_node, rows8042, irow8033, rows8043]
  all_goals rfl

theorem atot8033 : totK PA10K2 A10K2.u8033 = [0, 0, 0, 590588076907, 2884669665475, 4266495302427, 2039367944040, 200486634529, 0, 0] := by
  rw [show A10K2.u8033 = KTree.node A10K2.t8042 (nat_lit 132589282) (nat_lit 13752822675) (nat_lit 0) A10K2.t8043 from rfl, totK_node, tot8042, tot8043]
  decide +kernel

theorem arows8035 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8035 = true := by
  rw [show A10K2.u8035 = KTree.node A10K2.t8044 (nat_lit 132604513) (nat_lit 9776079216) (nat_lit 0) A10K2.t8045 from rfl, allE_node, rows8044, irow8035, rows8045]
  all_goals rfl

theorem atot8035 : totK PA10K2 A10K2.u8035 = [0, 0, 0, 868494622419, 3161049923381, 3895094168247, 1791363028122, 246312012206, 6860445330, 0] := by
  rw [show A10K2.u8035 = KTree.node A10K2.t8044 (nat_lit 132604513) (nat_lit 9776079216) (nat_lit 0) A10K2.t8045 from rfl, totK_node, tot8044, tot8045]
  decide +kernel

theorem arows8036 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8036 = true := by
  rw [show A10K2.u8036 = KTree.node A10K2.t8046 (nat_lit 132609266) (nat_lit 15042214456) (nat_lit 0) A10K2.t8047 from rfl, allE_node, rows8046, irow8036, rows8047]
  all_goals rfl

theorem atot8036 : totK PA10K2 A10K2.u8036 = [0, 0, 0, 0, 1218807967247, 4058539680996, 3766048488150, 889321770136, 30680040329, 0] := by
  rw [show A10K2.u8036 = KTree.node A10K2.t8046 (nat_lit 132609266) (nat_lit 15042214456) (nat_lit 0) A10K2.t8047 from rfl, totK_node, tot8046, tot8047]
  decide +kernel

theorem arows8040 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8040 = true := by
  rw [show A10K2.u8040 = KTree.node A10K2.t8048 (nat_lit 132721307) (nat_lit 9948771239) (nat_lit 0) A10K2.t8049 from rfl, allE_node, rows8048, irow8040, rows8049]
  all_goals rfl

theorem atot8040 : totK PA10K2 A10K2.u8040 = [0, 0, 849867569785, 3317100133176, 3946579519504, 1369955628591, 147134895982, 115725574594, 31688522620, 0] := by
  rw [show A10K2.u8040 = KTree.node A10K2.t8048 (nat_lit 132721307) (nat_lit 9948771239) (nat_lit 0) A10K2.t8049 from rfl, totK_node, tot8048, tot8049]
  decide +kernel

theorem arows8041 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8041 = true := by
  rw [show A10K2.u8041 = KTree.node A10K2.t8050 (nat_lit 132725973) (nat_lit 5626692054) (nat_lit 0) A10K2.t8051 from rfl, allE_node, rows8050, irow8041, rows8051]
  all_goals rfl

theorem atot8041 : totK PA10K2 A10K2.u8041 = [0, 0, 485530384623, 2205384369890, 3704006224030, 2611871018347, 582778558332, 31768748853, 0, 0] := by
  rw [show A10K2.u8041 = KTree.node A10K2.t8050 (nat_lit 132725973) (nat_lit 5626692054) (nat_lit 0) A10K2.t8051 from rfl, totK_node, tot8050, tot8051]
  decide +kernel

theorem arows8043 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8043 = true := by
  rw [show A10K2.u8043 = KTree.node A10K2.t8052 (nat_lit 132733728) (nat_lit 12074215859) (nat_lit 0) A10K2.t8053 from rfl, allE_node, rows8052, irow8043, rows8053]
  all_goals rfl

theorem atot8043 : totK PA10K2 A10K2.u8043 = [0, 0, 588515137096, 2875284196897, 4195470366148, 1794748627426, 229412540415, 5982052406, 0, 0] := by
  rw [show A10K2.u8043 = KTree.node A10K2.t8052 (nat_lit 132733728) (nat_lit 12074215859) (nat_lit 0) A10K2.t8053 from rfl, totK_node, tot8052, tot8053]
  decide +kernel

theorem arows8044 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8044 = true := by
  rw [show A10K2.u8044 = KTree.node A10K2.t8054 (nat_lit 132739986) (nat_lit 14104824767) (nat_lit 0) A10K2.t8055 from rfl, allE_node, rows8054, irow8044, rows8055]
  all_goals rfl

theorem atot8044 : totK PA10K2 A10K2.u8044 = [0, 0, 314234800528, 1956536402536, 4114473348439, 3120247787658, 635130779195, 19395622282, 0, 0] := by
  rw [show A10K2.u8044 = KTree.node A10K2.t8054 (nat_lit 132739986) (nat_lit 14104824767) (nat_lit 0) A10K2.t8055 from rfl, totK_node, tot8054, tot8055]
  decide +kernel

theorem arows8047 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8047 = true := by
  rw [show A10K2.u8047 = KTree.node A10K2.t8056 (nat_lit 132753622) (nat_lit 13334845768) (nat_lit 0) A10K2.t8057 from rfl, allE_node, rows8056, irow8047, rows8057]
  all_goals rfl

theorem atot8047 : totK PA10K2 A10K2.u8047 = [0, 0, 0, 845845233233, 3380310189946, 4030807874183, 1416655262739, 110316983856, 0, 0] := by
  rw [show A10K2.u8047 = KTree.node A10K2.t8056 (nat_lit 132753622) (nat_lit 13334845768) (nat_lit 0) A10K2.t8057 from rfl, totK_node, tot8056, tot8057]
  decide +kernel

theorem arows8048 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8048 = true := by
  rw [show A10K2.u8048 = KTree.node A10K2.t8058 (nat_lit 132758701) (nat_lit 5436272775) (nat_lit 0) A10K2.t8059 from rfl, allE_node, rows8058, irow8048, rows8059]
  all_goals rfl

theorem atot8048 : totK PA10K2 A10K2.u8048 = [0, 0, 0, 507603773640, 2308088379489, 3864775738573, 2427583045927, 438169381883, 13576218110, 0] := by
  rw [show A10K2.u8048 = KTree.node A10K2.t8058 (nat_lit 132758701) (nat_lit 5436272775) (nat_lit 0) A10K2.t8059 from rfl, totK_node, tot8058, tot8059]
  decide +kernel

theorem arows8050 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8050 = true := by
  rw [show A10K2.u8050 = KTree.node A10K2.t8060 (nat_lit 132768197) (nat_lit 1697877917) (nat_lit 0) A10K2.t8061 from rfl, allE_node, rows8060, irow8050, rows8061]
  all_goals rfl

theorem atot8050 : totK PA10K2 A10K2.u8050 = [0, 0, 0, 758681157820, 3344836083075, 4215007269737, 1402225799833, 83609018872, 0, 0] := by
  rw [show A10K2.u8050 = KTree.node A10K2.t8060 (nat_lit 132768197) (nat_lit 1697877917) (nat_lit 0) A10K2.t8061 from rfl, totK_node, tot8060, tot8061]
  decide +kernel

theorem arows8051 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8051 = true := by
  rw [show A10K2.u8051 = KTree.node A10K2.t8062 (nat_lit 132786002) (nat_lit 14828695722) (nat_lit 0) A10K2.t8063 from rfl, allE_node, rows8062, irow8051, rows8063]
  all_goals rfl

theorem atot8051 : totK PA10K2 A10K2.u8051 = [0, 0, 762716802215, 2903245991340, 3689790483772, 2008410433089, 577655525128, 50499610055, 0, 0] := by
  rw [show A10K2.u8051 = KTree.node A10K2.t8062 (nat_lit 132786002) (nat_lit 14828695722) (nat_lit 0) A10K2.t8063 from rfl, totK_node, tot8062, tot8063]
  decide +kernel

theorem arows8058 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8058 = true := by
  rw [show A10K2.u8058 = KTree.node A10K2.t8064 (nat_lit 132791122) (nat_lit 13710285956) (nat_lit 0) A10K2.t8065 from rfl, allE_node, rows8064, irow8058, rows8065]
  all_goals rfl

theorem atot8058 : totK PA10K2 A10K2.u8058 = [0, 0, 449094844100, 2188444074586, 3831266590881, 2640582728242, 599801601697, 31543789865, 0, 0] := by
  rw [show A10K2.u8058 = KTree.node A10K2.t8064 (nat_lit 132791122) (nat_lit 13710285956) (nat_lit 0) A10K2.t8065 from rfl, totK_node, tot8064, tot8065]
  decide +kernel

theorem arows8059 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8059 = true := by
  rw [show A10K2.u8059 = KTree.node A10K2.t8066 (nat_lit 132819102) (nat_lit 12763132209) (nat_lit 0) A10K2.t8067 from rfl, allE_node, rows8066, irow8059, rows8067]
  all_goals rfl

theorem atot8059 : totK PA10K2 A10K2.u8059 = [0, 0, 109259794108, 1569348498242, 4037686267081, 3283235801191, 780050248590, 39344277108, 0, 0] := by
  rw [show A10K2.u8059 = KTree.node A10K2.t8066 (nat_lit 132819102) (nat_lit 12763132209) (nat_lit 0) A10K2.t8067 from rfl, totK_node, tot8066, tot8067]
  decide +kernel

theorem arows8061 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8061 = true := by
  rw [show A10K2.u8061 = KTree.node A10K2.t8068 (nat_lit 132842062) (nat_lit 10064272317) (nat_lit 0) A10K2.t8069 from rfl, allE_node, rows8068, irow8061, rows8069]
  all_goals rfl

theorem atot8061 : totK PA10K2 A10K2.u8061 = [0, 0, 588716830688, 2714280294452, 4075878634443, 2184826878254, 297665367925, 6356241174, 0, 0] := by
  rw [show A10K2.u8061 = KTree.node A10K2.t8068 (nat_lit 132842062) (nat_lit 10064272317) (nat_lit 0) A10K2.t8069 from rfl, totK_node, tot8068, tot8069]
  decide +kernel

theorem arows8062 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8062 = true := by
  rw [show A10K2.u8062 = KTree.node A10K2.t8070 (nat_lit 132851346) (nat_lit 15872022006) (nat_lit 0) A10K2.t8071 from rfl, allE_node, rows8070, irow8062, rows8071]
  all_goals rfl

theorem atot8062 : totK PA10K2 A10K2.u8062 = [0, 0, 796254824344, 3060211275964, 3913054319806, 1874717023769, 320423171434, 12462147902, 0, 0] := by
  rw [show A10K2.u8062 = KTree.node A10K2.t8070 (nat_lit 132851346) (nat_lit 15872022006) (nat_lit 0) A10K2.t8071 from rfl, totK_node, tot8070, tot8071]
  decide +kernel

theorem arows8065 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8065 = true := by
  rw [show A10K2.u8065 = KTree.node A10K2.t8072 (nat_lit 132856090) (nat_lit 14174292022) (nat_lit 0) A10K2.t8073 from rfl, allE_node, rows8072, irow8065, rows8073]
  all_goals rfl

theorem atot8065 : totK PA10K2 A10K2.u8065 = [0, 0, 253046812372, 1905054479856, 4121307152414, 2956332685114, 573568261880, 18710738642, 0, 0] := by
  rw [show A10K2.u8065 = KTree.node A10K2.t8072 (nat_lit 132856090) (nat_lit 14174292022) (nat_lit 0) A10K2.t8073 from rfl, totK_node, tot8072, tot8073]
  decide +kernel

theorem arows8066 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8066 = true := by
  rw [show A10K2.u8066 = KTree.node A10K2.t8074 (nat_lit 132869677) (nat_lit 1292671088) (nat_lit 0) A10K2.t8075 from rfl, allE_node, rows8074, irow8066, rows8075]
  all_goals rfl

theorem atot8066 : totK PA10K2 A10K2.u8066 = [0, 0, 615603840132, 2779136411642, 4106621340590, 2172546699199, 318169913290, 6853348008, 0, 0] := by
  rw [show A10K2.u8066 = KTree.node A10K2.t8074 (nat_lit 132869677) (nat_lit 1292671088) (nat_lit 0) A10K2.t8075 from rfl, totK_node, tot8074, tot8075]
  decide +kernel

theorem arows8068 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8068 = true := by
  rw [show A10K2.u8068 = KTree.node A10K2.t8076 (nat_lit 132874239) (nat_lit 13968960306) (nat_lit 0) A10K2.t8077 from rfl, allE_node, rows8076, irow8068, rows8077]
  all_goals rfl

theorem atot8068 : totK PA10K2 A10K2.u8068 = [0, 0, 0, 982865352788, 3711609660665, 4085210742770, 1254314084180, 75412782266, 0, 0] := by
  rw [show A10K2.u8068 = KTree.node A10K2.t8076 (nat_lit 132874239) (nat_lit 13968960306) (nat_lit 0) A10K2.t8077 from rfl, totK_node, tot8076, tot8077]
  decide +kernel

theorem arows8069 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8069 = true := by
  rw [show A10K2.u8069 = KTree.node A10K2.t8078 (nat_lit 132881913) (nat_lit 6311572477) (nat_lit 0) A10K2.t8079 from rfl, allE_node, rows8078, irow8069, rows8079]
  all_goals rfl

theorem atot8069 : totK PA10K2 A10K2.u8069 = [0, 0, 0, 568700286610, 2676486484169, 4135938825959, 2176776518133, 288166959437, 6632180018, 0] := by
  rw [show A10K2.u8069 = KTree.node A10K2.t8078 (nat_lit 132881913) (nat_lit 6311572477) (nat_lit 0) A10K2.t8079 from rfl, totK_node, tot8078, tot8079]
  decide +kernel

theorem arows8073 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8073 = true := by
  rw [show A10K2.u8073 = KTree.node A10K2.t8080 (nat_lit 132888250) (nat_lit 14613938373) (nat_lit 0) A10K2.t8081 from rfl, allE_node, rows8080, irow8073, rows8081]
  all_goals rfl

theorem atot8073 : totK PA10K2 A10K2.u8073 = [0, 0, 0, 480234610980, 2540839386755, 4212165116048, 2362586408899, 321268362918, 7047025452, 0] := by
  rw [show A10K2.u8073 = KTree.node A10K2.t8080 (nat_lit 132888250) (nat_lit 14613938373) (nat_lit 0) A10K2.t8081 from rfl, totK_node, tot8080, tot8081]
  decide +kernel

theorem arows8074 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8074 = true := by
  rw [show A10K2.u8074 = KTree.node A10K2.t8082 (nat_lit 132902359) (nat_lit 14430147840) (nat_lit 0) A10K2.t8083 from rfl, allE_node, rows8082, irow8074, rows8083]
  all_goals rfl

theorem atot8074 : totK PA10K2 A10K2.u8074 = [0, 0, 0, 615115902947, 2802014998497, 4120442683868, 2092042935980, 266947021256, 6066958478, 0] := by
  rw [show A10K2.u8074 = KTree.node A10K2.t8082 (nat_lit 132902359) (nat_lit 14430147840) (nat_lit 0) A10K2.t8083 from rfl, totK_node, tot8082, tot8083]
  decide +kernel

theorem arows8076 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8076 = true := by
  rw [show A10K2.u8076 = KTree.node A10K2.t8084 (nat_lit 132906967) (nat_lit 14215013275) (nat_lit 0) A10K2.t8085 from rfl, allE_node, rows8084, irow8076, rows8085]
  all_goals rfl

theorem atot8076 : totK PA10K2 A10K2.u8076 = [0, 0, 0, 552913550463, 2338820964171, 3545092444621, 2557579880769, 738661170223, 55043167628, 0] := by
  rw [show A10K2.u8076 = KTree.node A10K2.t8084 (nat_lit 132906967) (nat_lit 14215013275) (nat_lit 0) A10K2.t8085 from rfl, totK_node, tot8084, tot8085]
  decide +kernel

theorem arows8077 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8077 = true := by
  rw [show A10K2.u8077 = KTree.node A10K2.t8086 (nat_lit 132986263) (nat_lit 14237883125) (nat_lit 0) A10K2.t8087 from rfl, allE_node, rows8086, irow8077, rows8087]
  all_goals rfl

theorem atot8077 : totK PA10K2 A10K2.u8077 = [0, 0, 0, 292221444102, 2021916707609, 4218969470034, 2762576864710, 451260277745, 13576218110, 0] := by
  rw [show A10K2.u8077 = KTree.node A10K2.t8086 (nat_lit 132986263) (nat_lit 14237883125) (nat_lit 0) A10K2.t8087 from rfl, totK_node, tot8086, tot8087]
  decide +kernel

theorem arows8080 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8080 = true := by
  rw [show A10K2.u8080 = KTree.node A10K2.t8088 (nat_lit 132991752) (nat_lit 8859963045) (nat_lit 0) A10K2.t8089 from rfl, allE_node, rows8088, irow8080, rows8089]
  all_goals rfl

theorem atot8080 : totK PA10K2 A10K2.u8080 = [0, 0, 0, 774624675675, 3223986008299, 4064221697741, 1523767205435, 123796697599, 0, 0] := by
  rw [show A10K2.u8080 = KTree.node A10K2.t8088 (nat_lit 132991752) (nat_lit 8859963045) (nat_lit 0) A10K2.t8089 from rfl, totK_node, tot8088, tot8089]
  decide +kernel

theorem arows8081 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8081 = true := by
  rw [show A10K2.u8081 = KTree.node A10K2.t8090 (nat_lit 133000762) (nat_lit 11499283544) (nat_lit 0) A10K2.t8091 from rfl, allE_node, rows8090, irow8081, rows8091]
  all_goals rfl

theorem atot8081 : totK PA10K2 A10K2.u8081 = [0, 0, 0, 611103909717, 2726504808488, 4164881116238, 2272543636752, 315036143398, 6962742351, 0] := by
  rw [show A10K2.u8081 = KTree.node A10K2.t8090 (nat_lit 133000762) (nat_lit 11499283544) (nat_lit 0) A10K2.t8091 from rfl, totK_node, tot8090, tot8091]
  decide +kernel

theorem arows8083 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8083 = true := by
  rw [show A10K2.u8083 = KTree.node A10K2.t8092 (nat_lit 133014921) (nat_lit 2388803552) (nat_lit 0) A10K2.t8093 from rfl, allE_node, rows8092, irow8083, rows8093]
  all_goals rfl

theorem atot8083 : totK PA10K2 A10K2.u8083 = [0, 0, 0, 0, 1140820261958, 3887994674268, 3742647757446, 951197269755, 47704591184, 0] := by
  rw [show A10K2.u8083 = KTree.node A10K2.t8092 (nat_lit 133014921) (nat_lit 2388803552) (nat_lit 0) A10K2.t8093 from rfl, totK_node, tot8092, tot8093]
  decide +kernel

theorem arows8084 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8084 = true := by
  rw [show A10K2.u8084 = KTree.node A10K2.t8094 (nat_lit 133020819) (nat_lit 10901359787) (nat_lit 0) A10K2.t8095 from rfl, allE_node, rows8094, irow8084, rows8095]
  all_goals rfl

theorem atot8084 : totK PA10K2 A10K2.u8084 = [0, 0, 0, 0, 693003297685, 2970791611896, 3946335718526, 1813663291830, 241060907056, 7380853412] := by
  rw [show A10K2.u8084 = KTree.node A10K2.t8094 (nat_lit 133020819) (nat_lit 10901359787) (nat_lit 0) A10K2.t8095 from rfl, totK_node, tot8094, tot8095]
  decide +kernel

theorem arows8089 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8089 = true := by
  rw [show A10K2.u8089 = KTree.node A10K2.t8096 (nat_lit 133033478) (nat_lit 15176269704) (nat_lit 0) A10K2.t8097 from rfl, allE_node, rows8096, irow8089, rows8097]
  all_goals rfl

theorem atot8089 : totK PA10K2 A10K2.u8089 = [0, 0, 0, 442678411980, 2130044460875, 3826124350169, 2884195324027, 725761392094, 43953344306, 0] := by
  rw [show A10K2.u8089 = KTree.node A10K2.t8096 (nat_lit 133033478) (nat_lit 15176269704) (nat_lit 0) A10K2.t8097 from rfl, totK_node, tot8096, tot8097]
  decide +kernel

theorem arows8090 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8090 = true := by
  rw [show A10K2.u8090 = KTree.node A10K2.t8098 (nat_lit 133055954) (nat_lit 15096014141) (nat_lit 0) A10K2.t8099 from rfl, allE_node, rows8098, irow8090, rows8099]
  all_goals rfl

theorem atot8090 : totK PA10K2 A10K2.u8090 = [0, 0, 0, 1150634717201, 4004826916572, 3643543940017, 898103505569, 37968628945, 0, 0] := by
  rw [show A10K2.u8090 = KTree.node A10K2.t8098 (nat_lit 133055954) (nat_lit 15096014141) (nat_lit 0) A10K2.t8099 from rfl, totK_node, tot8098, tot8099]
  decide +kernel

theorem arows8092 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8092 = true := by
  rw [show A10K2.u8092 = KTree.node A10K2.t8100 (nat_lit 133108225) (nat_lit 10551639029) (nat_lit 0) A10K2.t8101 from rfl, allE_node, rows8100, irow8092, rows8101]
  all_goals rfl

theorem atot8092 : totK PA10K2 A10K2.u8092 = [0, 0, 0, 613156518497, 2757010647107, 4140124453015, 2201522040075, 291975589823, 6725424603, 0] := by
  rw [show A10K2.u8092 = KTree.node A10K2.t8100 (nat_lit 133108225) (nat_lit 10551639029) (nat_lit 0) A10K2.t8101 from rfl, totK_node, tot8100, tot8101]
  decide +kernel

theorem arows8093 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8093 = true := by
  rw [show A10K2.u8093 = KTree.node A10K2.t8102 (nat_lit 133115827) (nat_lit 9302984323) (nat_lit 0) A10K2.t8103 from rfl, allE_node, rows8102, irow8093, rows8103]
  all_goals rfl

theorem atot8093 : totK PA10K2 A10K2.u8093 = [0, 0, 0, 483448716589, 2455488973107, 4093959317506, 2413186047037, 364007121407, 12692412833, 0] := by
  rw [show A10K2.u8093 = KTree.node A10K2.t8102 (nat_lit 133115827) (nat_lit 9302984323) (nat_lit 0) A10K2.t8103 from rfl, totK_node, tot8102, tot8103]
  decide +kernel

theorem arows8096 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8096 = true := by
  rw [show A10K2.u8096 = KTree.node A10K2.t8104 (nat_lit 133129651) (nat_lit 9841975983) (nat_lit 0) A10K2.t8105 from rfl, allE_node, rows8104, irow8096, rows8105]
  all_goals rfl

theorem atot8096 : totK PA10K2 A10K2.u8096 = [0, 0, 0, 867047146108, 3403950638442, 4115769185456, 1514516147779, 105160204383, 0, 0] := by
  rw [show A10K2.u8096 = KTree.node A10K2.t8104 (nat_lit 133129651) (nat_lit 9841975983) (nat_lit 0) A10K2.t8105 from rfl, totK_node, tot8104, tot8105]
  decide +kernel

theorem arows8097 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8097 = true := by
  rw [show A10K2.u8097 = KTree.node A10K2.t8106 (nat_lit 133134257) (nat_lit 7423382353) (nat_lit 0) A10K2.t8107 from rfl, allE_node, rows8106, irow8097, rows8107]
  all_goals rfl

theorem atot8097 : totK PA10K2 A10K2.u8097 = [0, 0, 310694887869, 690619871721, 1179110208827, 3213115873672, 3444184166190, 982101843566, 62382159641, 0] := by
  rw [show A10K2.u8097 = KTree.node A10K2.t8106 (nat_lit 133134257) (nat_lit 7423382353) (nat_lit 0) A10K2.t8107 from rfl, totK_node, tot8106, tot8107]
  decide +kernel

theorem arows8099 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8099 = true := by
  rw [show A10K2.u8099 = KTree.node A10K2.t8108 (nat_lit 133696969) (nat_lit 6782221256) (nat_lit 0) A10K2.t8109 from rfl, allE_node, rows8108, irow8099, rows8109]
  all_goals rfl

theorem atot8099 : totK PA10K2 A10K2.u8099 = [0, 0, 496719956537, 2597001280095, 4048478748648, 2110956983259, 400222169352, 18469913835, 0, 0] := by
  rw [show A10K2.u8099 = KTree.node A10K2.t8108 (nat_lit 133696969) (nat_lit 6782221256) (nat_lit 0) A10K2.t8109 from rfl, totK_node, tot8108, tot8109]
  decide +kernel

theorem arows8100 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8100 = true := by
  rw [show A10K2.u8100 = KTree.node A10K2.t8110 (nat_lit 133710387) (nat_lit 1980391044) (nat_lit 0) A10K2.t8111 from rfl, allE_node, rows8110, irow8100, rows8111]
  all_goals rfl

theorem atot8100 : totK PA10K2 A10K2.u8100 = [0, 0, 554054383230, 2711350268305, 4178902662979, 1937690205065, 209262221964, 0, 0, 0] := by
  rw [show A10K2.u8100 = KTree.node A10K2.t8110 (nat_lit 133710387) (nat_lit 1980391044) (nat_lit 0) A10K2.t8111 from rfl, totK_node, tot8110, tot8111]
  decide +kernel

theorem arows8104 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8104 = true := by
  rw [show A10K2.u8104 = KTree.node A10K2.t8112 (nat_lit 133721237) (nat_lit 4283910200) (nat_lit 0) A10K2.t8113 from rfl, allE_node, rows8112, irow8104, rows8113]
  all_goals rfl

theorem atot8104 : totK PA10K2 A10K2.u8104 = [0, 0, 719492328128, 3051362229193, 4157016218706, 1923065915989, 272283955031, 6853348008, 0, 0] := by
  rw [show A10K2.u8104 = KTree.node A10K2.t8112 (nat_lit 133721237) (nat_lit 4283910200) (nat_lit 0) A10K2.t8113 from rfl, totK_node, tot8112, tot8113]
  decide +kernel

theorem arows8105 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8105 = true := by
  rw [show A10K2.u8105 = KTree.node A10K2.t8114 (nat_lit 133725880) (nat_lit 11228070276) (nat_lit 0) A10K2.t8115 from rfl, allE_node, rows8114, irow8105, rows8115]
  all_goals rfl

theorem atot8105 : totK PA10K2 A10K2.u8105 = [0, 0, 0, 1048774491971, 3700895338510, 3941066379395, 1186049126866, 74763712556, 0, 0] := by
  rw [show A10K2.u8105 = KTree.node A10K2.t8114 (nat_lit 133725880) (nat_lit 11228070276) (nat_lit 0) A10K2.t8115 from rfl, totK_node, tot8114, tot8115]
  decide +kernel

theorem arows8107 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8107 = true := by
  rw [show A10K2.u8107 = KTree.node A10K2.t8116 (nat_lit 133730668) (nat_lit 9687832308) (nat_lit 8) A10K2.t8117 from rfl, allE_node, rows8116, irow8107, rows8117]
  all_goals rfl

theorem atot8107 : totK PA10K2 A10K2.u8107 = [0, 0, 0, 407673814617, 2337068224543, 4102948271438, 2323775700110, 356416982455, 12477124820, 0] := by
  rw [show A10K2.u8107 = KTree.node A10K2.t8116 (nat_lit 133730668) (nat_lit 9687832308) (nat_lit 8) A10K2.t8117 from rfl, totK_node, tot8116, tot8117]
  decide +kernel

theorem arows8108 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8108 = true := by
  rw [show A10K2.u8108 = KTree.node A10K2.t8118 (nat_lit 133748736) (nat_lit 15028179709) (nat_lit 0) A10K2.t8119 from rfl, allE_node, rows8118, irow8108, rows8119]
  all_goals rfl

theorem atot8108 : totK PA10K2 A10K2.u8108 = [0, 0, 0, 838462949914, 3529033908082, 4143293128677, 1193167925777, 51103524074, 0, 0] := by
  rw [show A10K2.u8108 = KTree.node A10K2.t8118 (nat_lit 133748736) (nat_lit 15028179709) (nat_lit 0) A10K2.t8119 from rfl, totK_node, tot8118, tot8119]
  decide +kernel

theorem arows8111 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8111 = true := by
  rw [show A10K2.u8111 = KTree.node A10K2.t8120 (nat_lit 133768552) (nat_lit 5733146015) (nat_lit 0) A10K2.t8121 from rfl, allE_node, rows8120, irow8111, rows8121]
  all_goals rfl

theorem atot8111 : totK PA10K2 A10K2.u8111 = [0, 0, 726864767559, 2704531867617, 3507109626900, 2195562142756, 696890738663, 57551169768, 0, 0] := by
  rw [show A10K2.u8111 = KTree.node A10K2.t8120 (nat_lit 133768552) (nat_lit 5733146015) (nat_lit 0) A10K2.t8121 from rfl, totK_node, tot8120, tot8121]
  decide +kernel

theorem arows8112 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8112 = true := by
  rw [show A10K2.u8112 = KTree.node A10K2.t8122 (nat_lit 133773184) (nat_lit 8946476067) (nat_lit 0) A10K2.t8123 from rfl, allE_node, rows8122, irow8112, rows8123]
  all_goals rfl

theorem atot8112 : totK PA10K2 A10K2.u8112 = [0, 0, 357007200198, 2040284710986, 3978697575068, 2838894298643, 557550184621, 18722998264, 0, 0] := by
  rw [show A10K2.u8112 = KTree.node A10K2.t8122 (nat_lit 133773184) (nat_lit 8946476067) (nat_lit 0) A10K2.t8123 from rfl, totK_node, tot8122, tot8123]
  decide +kernel

theorem arows8114 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8114 = true := by
  rw [show A10K2.u8114 = KTree.node A10K2.t8124 (nat_lit 133783601) (nat_lit 9920846398) (nat_lit 0) A10K2.t8125 from rfl, allE_node, rows8124, irow8114, rows8125]
  all_goals rfl

theorem atot8114 : totK PA10K2 A10K2.u8114 = [0, 0, 760134419890, 3292177435431, 4308835832615, 1478598513823, 96359347835, 0, 0, 0] := by
  rw [show A10K2.u8114 = KTree.node A10K2.t8124 (nat_lit 133783601) (nat_lit 9920846398) (nat_lit 0) A10K2.t8125 from rfl, totK_node, tot8124, tot8125]
  decide +kernel

theorem arows8115 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8115 = true := by
  rw [show A10K2.u8115 = KTree.node A10K2.t8126 (nat_lit 133788551) (nat_lit 14425336065) (nat_lit 0) A10K2.t8127 from rfl, allE_node, rows8126, irow8115, rows8127]
  all_goals rfl

theorem atot8115 : totK PA10K2 A10K2.u8115 = [0, 0, 244336036153, 1913939918350, 4232245673154, 3244156511534, 634838704927, 13814447077, 0, 0] := by
  rw [show A10K2.u8115 = KTree.node A10K2.t8126 (nat_lit 133788551) (nat_lit 14425336065) (nat_lit 0) A10K2.t8127 from rfl, totK_node, tot8126, tot8127]
  decide +kernel

theorem arows8121 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8121 = true := by
  rw [show A10K2.u8121 = KTree.node A10K2.t8128 (nat_lit 133802205) (nat_lit 5725859541) (nat_lit 0) A10K2.t8129 from rfl, allE_node, rows8128, irow8121, rows8129]
  all_goals rfl

theorem atot8121 : totK PA10K2 A10K2.u8121 = [0, 0, 0, 809946247554, 3274930676833, 4029493026693, 1517322526834, 121895375620, 0, 0] := by
  rw [show A10K2.u8121 = KTree.node A10K2.t8128 (nat_lit 133802205) (nat_lit 5725859541) (nat_lit 0) A10K2.t8129 from rfl, totK_node, tot8128, tot8129]
  decide +kernel

theorem arows8122 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8122 = true := by
  rw [show A10K2.u8122 = KTree.node A10K2.t8130 (nat_lit 133807558) (nat_lit 14887955241) (nat_lit 0) A10K2.t8131 from rfl, allE_node, rows8130, irow8122, rows8131]
  all_goals rfl

theorem atot8122 : totK PA10K2 A10K2.u8122 = [0, 0, 0, 443742495885, 2400490771874, 3993286453042, 2281485498383, 347125837974, 12696458652, 0] := by
  rw [show A10K2.u8122 = KTree.node A10K2.t8130 (nat_lit 133807558) (nat_lit 14887955241) (nat_lit 0) A10K2.t8131 from rfl, totK_node, tot8130, tot8131]
  decide +kernel

theorem arows8124 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8124 = true := by
  rw [show A10K2.u8124 = KTree.node A10K2.t8132 (nat_lit 133818019) (nat_lit 10571254891) (nat_lit 0) A10K2.t8133 from rfl, allE_node, rows8132, irow8124, rows8133]
  all_goals rfl

theorem atot8124 : totK PA10K2 A10K2.u8124 = [0, 0, 113839911969, 1063623363412, 3368513623249, 4070161837704, 1388673415226, 81989397432, 0, 0] := by
  rw [show A10K2.u8124 = KTree.node A10K2.t8132 (nat_lit 133818019) (nat_lit 10571254891) (nat_lit 0) A10K2.t8133 from rfl, totK_node, tot8132, tot8133]
  decide +kernel

theorem arows8125 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8125 = true := by
  rw [show A10K2.u8125 = KTree.node A10K2.t8134 (nat_lit 133893361) (nat_lit 6111969076) (nat_lit 0) A10K2.t8135 from rfl, allE_node, rows8134, irow8125, rows8135]
  all_goals rfl

theorem atot8125 : totK PA10K2 A10K2.u8125 = [0, 0, 648198587954, 2850447630324, 3933201349443, 1892444017926, 323129165638, 17500500512, 0, 0] := by
  rw [show A10K2.u8125 = KTree.node A10K2.t8134 (nat_lit 133893361) (nat_lit 6111969076) (nat_lit 0) A10K2.t8135 from rfl, totK_node, tot8134, tot8135]
  decide +kernel

theorem arows8128 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8128 = true := by
  rw [show A10K2.u8128 = KTree.node A10K2.t8136 (nat_lit 133899763) (nat_lit 9023718657) (nat_lit 0) A10K2.t8137 from rfl, allE_node, rows8136, irow8128, rows8137]
  all_goals rfl

theorem atot8128 : totK PA10K2 A10K2.u8128 = [0, 0, 765763168051, 3067765564356, 3977191535258, 1815595401114, 223189667162, 0, 0, 0] := by
  rw [show A10K2.u8128 = KTree.node A10K2.t8136 (nat_lit 133899763) (nat_lit 9023718657) (nat_lit 0) A10K2.t8137 from rfl, totK_node, tot8136, tot8137]
  decide +kernel

theorem arows8129 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8129 = true := by
  rw [show A10K2.u8129 = KTree.node A10K2.t8138 (nat_lit 133904739) (nat_lit 7339712645) (nat_lit 32) A10K2.t8139 from rfl, allE_node, rows8138, irow8129, rows8139]
  all_goals rfl

theorem atot8129 : totK PA10K2 A10K2.u8129 = [0, 0, 281204290441, 1994748310616, 4126405065222, 2834224274132, 527817638988, 17754888877, 0, 0] := by
  rw [show A10K2.u8129 = KTree.node A10K2.t8138 (nat_lit 133904739) (nat_lit 7339712645) (nat_lit 32) A10K2.t8139 from rfl, totK_node, tot8138, tot8139]
  decide +kernel

theorem arows8131 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8131 = true := by
  rw [show A10K2.u8131 = KTree.node A10K2.t8140 (nat_lit 133918264) (nat_lit 14672681569) (nat_lit 0) A10K2.t8141 from rfl, allE_node, rows8140, irow8131, rows8141]
  all_goals rfl

theorem atot8131 : totK PA10K2 A10K2.u8131 = [0, 0, 615230447397, 2710681063258, 4085863398559, 2224235996330, 327348689313, 6853348008, 0, 0] := by
  rw [show A10K2.u8131 = KTree.node A10K2.t8140 (nat_lit 133918264) (nat_lit 14672681569) (nat_lit 0) A10K2.t8141 from rfl, totK_node, tot8140, tot8141]
  decide +kernel

theorem arows8132 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8132 = true := by
  rw [show A10K2.u8132 = KTree.node A10K2.t8142 (nat_lit 133922779) (nat_lit 5676682112) (nat_lit 0) A10K2.t8143 from rfl, allE_node, rows8142, irow8132, rows8143]
  all_goals rfl

theorem atot8132 : totK PA10K2 A10K2.u8132 = [0, 0, 0, 1005010780091, 3668182844123, 3944110058325, 1170982058976, 73684606545, 0, 0] := by
  rw [show A10K2.u8132 = KTree.node A10K2.t8142 (nat_lit 133922779) (nat_lit 5676682112) (nat_lit 0) A10K2.t8143 from rfl, totK_node, tot8142, tot8143]
  decide +kernel

theorem arows8136 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8136 = true := by
  rw [show A10K2.u8136 = KTree.node A10K2.t8144 (nat_lit 133927502) (nat_lit 9966385053) (nat_lit 0) A10K2.t8145 from rfl, allE_node, rows8144, irow8136, rows8145]
  all_goals rfl

theorem atot8136 : totK PA10K2 A10K2.u8136 = [0, 0, 0, 499024904369, 2580636229503, 4180626648036, 2233818283806, 301962251734, 6904928264, 0] := by
  rw [show A10K2.u8136 = KTree.node A10K2.t8144 (nat_lit 133927502) (nat_lit 9966385053) (nat_lit 0) A10K2.t8145 from rfl, totK_node, tot8144, tot8145]
  decide +kernel

theorem arows8137 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8137 = true := by
  rw [show A10K2.u8137 = KTree.node A10K2.t8146 (nat_lit 133934818) (nat_lit 13294330769) (nat_lit 0) A10K2.t8147 from rfl, allE_node, rows8146, irow8137, rows8147]
  all_goals rfl

theorem atot8137 : totK PA10K2 A10K2.u8137 = [0, 0, 0, 466273731196, 2528489252619, 4228478172564, 2262900664910, 284376703523, 7047025452, 0] := by
  rw [show A10K2.u8137 = KTree.node A10K2.t8146 (nat_lit 133934818) (nat_lit 13294330769) (nat_lit 0) A10K2.t8147 from rfl, totK_node, tot8146, tot8147]
  decide +kernel

theorem arows8139 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8139 = true := by
  rw [show A10K2.u8139 = KTree.node A10K2.t8148 (nat_lit 133949074) (nat_lit 15830774048) (nat_lit 0) A10K2.t8149 from rfl, allE_node, rows8148, irow8139, rows8149]
  all_goals rfl

theorem atot8139 : totK PA10K2 A10K2.u8139 = [0, 0, 0, 895145480297, 3450982898853, 4046322536623, 1437748180966, 113376364670, 0, 0] := by
  rw [show A10K2.u8139 = KTree.node A10K2.t8148 (nat_lit 133949074) (nat_lit 15830774048) (nat_lit 0) A10K2.t8149 from rfl, totK_node, tot8148, tot8149]
  decide +kernel

theorem arows8140 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8140 = true := by
  rw [show A10K2.u8140 = KTree.node A10K2.t8150 (nat_lit 133954622) (nat_lit 16101479194) (nat_lit 0) A10K2.t8151 from rfl, allE_node, rows8150, irow8140, rows8151]
  all_goals rfl

theorem atot8140 : totK PA10K2 A10K2.u8140 = [0, 0, 0, 309157067044, 1661993594220, 3562995042037, 3313706501251, 918115980813, 61110126106, 0] := by
  rw [show A10K2.u8140 = KTree.node A10K2.t8150 (nat_lit 133954622) (nat_lit 16101479194) (nat_lit 0) A10K2.t8151 from rfl, totK_node, tot8150, tot8151]
  decide +kernel

theorem arows8143 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8143 = true := by
  rw [show A10K2.u8143 = KTree.node A10K2.t8152 (nat_lit 133959236) (nat_lit 10231280260) (nat_lit 0) A10K2.t8153 from rfl, allE_node, rows8152, irow8143, rows8153]
  all_goals rfl

theorem atot8143 : totK PA10K2 A10K2.u8143 = [0, 0, 0, 496219520495, 2530087489906, 4019895525838, 2201711622538, 338875062418, 12477124820, 0] := by
  rw [show A10K2.u8143 = KTree.node A10K2.t8152 (nat_lit 133959236) (nat_lit 10231280260) (nat_lit 0) A10K2.t8153 from rfl, totK_node, tot8152, tot8153]
  decide +kernel

theorem arows8144 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8144 = true := by
  rw [show A10K2.u8144 = KTree.node A10K2.t8154 (nat_lit 133974029) (nat_lit 5823242822) (nat_lit 0) A10K2.t8155 from rfl, allE_node, rows8154, irow8144, rows8155]
  all_goals rfl

theorem atot8144 : totK PA10K2 A10K2.u8144 = [0, 0, 0, 730963051449, 2995309739107, 4087843272183, 1738903041073, 136806011845, 0, 0] := by
  rw [show A10K2.u8144 = KTree.node A10K2.t8154 (nat_lit 133974029) (nat_lit 5823242822) (nat_lit 0) A10K2.t8155 from rfl, totK_node, tot8154, tot8155]
  decide +kernel

theorem arows8146 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8146 = true := by
  rw [show A10K2.u8146 = KTree.node A10K2.t8156 (nat_lit 133983901) (nat_lit 3713777183) (nat_lit 0) A10K2.t8157 from rfl, allE_node, rows8156, irow8146, rows8157]
  all_goals rfl

theorem atot8146 : totK PA10K2 A10K2.u8146 = [0, 0, 0, 537680587155, 2616966640549, 4238960285749, 2422019618374, 344964600100, 6853348008, 0] := by
  rw [show A10K2.u8146 = KTree.node A10K2.t8156 (nat_lit 133983901) (nat_lit 3713777183) (nat_lit 0) A10K2.t8157 from rfl, totK_node, tot8156, tot8157]
  decide +kernel

theorem arows8147 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8147 = true := by
  rw [show A10K2.u8147 = KTree.node A10K2.t8158 (nat_lit 133988653) (nat_lit 6182980950) (nat_lit 0) A10K2.t8159 from rfl, allE_node, rows8158, irow8147, rows8159]
  all_goals rfl

theorem atot8147 : totK PA10K2 A10K2.u8147 = [0, 0, 0, 0, 1123384977303, 3827501218471, 3797505181865, 1018973941831, 67995113947, 0] := by
  rw [show A10K2.u8147 = KTree.node A10K2.t8158 (nat_lit 133988653) (nat_lit 6182980950) (nat_lit 0) A10K2.t8159 from rfl, totK_node, tot8158, tot8159]
  decide +kernel

theorem arows8152 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8152 = true := by
  rw [show A10K2.u8152 = KTree.node A10K2.t8160 (nat_lit 133995575) (nat_lit 14838044417) (nat_lit 0) A10K2.t8161 from rfl, allE_node, rows8160, irow8152, rows8161]
  all_goals rfl

theorem atot8152 : totK PA10K2 A10K2.u8152 = [0, 0, 0, 0, 696893510187, 2997898059363, 3886785767141, 1719528967427, 230980798152, 6725424603] := by
  rw [show A10K2.u8152 = KTree.node A10K2.t8160 (nat_lit 133995575) (nat_lit 14838044417) (nat_lit 0) A10K2.t8161 from rfl, totK_node, tot8160, tot8161]
  decide +kernel

theorem arows8153 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8153 = true := by
  rw [show A10K2.u8153 = KTree.node A10K2.t8162 (nat_lit 134016468) (nat_lit 5888964571) (nat_lit 0) A10K2.t8163 from rfl, allE_node, rows8162, irow8153, rows8163]
  all_goals rfl

theorem atot8153 : totK PA10K2 A10K2.u8153 = [0, 0, 0, 310599358184, 1671291537809, 3571129949097, 3362282710536, 1001766633881, 68492179993, 0] := by
  rw [show A10K2.u8153 = KTree.node A10K2.t8162 (nat_lit 134016468) (nat_lit 5888964571) (nat_lit 0) A10K2.t8163 from rfl, totK_node, tot8162, tot8163]
  decide +kernel

theorem arows8155 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8155 = true := by
  rw [show A10K2.u8155 = KTree.node A10K2.t8164 (nat_lit 134034590) (nat_lit 14766344110) (nat_lit 0) A10K2.t8165 from rfl, allE_node, rows8164, irow8155, rows8165]
  all_goals rfl

theorem atot8155 : totK PA10K2 A10K2.u8155 = [0, 0, 0, 498395592943, 2459840649292, 4058318677946, 2407252127198, 364280588395, 12696458652, 0] := by
  rw [show A10K2.u8155 = KTree.node A10K2.t8164 (nat_lit 134034590) (nat_lit 14766344110) (nat_lit 0) A10K2.t8165 from rfl, totK_node, tot8164, tot8165]
  decide +kernel

theorem arows8156 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8156 = true := by
  rw [show A10K2.u8156 = KTree.node A10K2.t8166 (nat_lit 134042906) (nat_lit 14495907466) (nat_lit 0) A10K2.t8167 from rfl, allE_node, rows8166, irow8156, rows8167]
  all_goals rfl

theorem atot8156 : totK PA10K2 A10K2.u8156 = [0, 0, 0, 951359521851, 3549319329754, 3924605257517, 1395701118283, 102218831672, 0, 0] := by
  rw [show A10K2.u8156 = KTree.node A10K2.t8166 (nat_lit 134042906) (nat_lit 14495907466) (nat_lit 0) A10K2.t8167 from rfl, totK_node, tot8166, tot8167]
  decide +kernel

theorem arows8159 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8159 = true := by
  rw [show A10K2.u8159 = KTree.node A10K2.t8168 (nat_lit 134049900) (nat_lit 5111782008) (nat_lit 0) A10K2.t8169 from rfl, allE_node, rows8168, irow8159, rows8169]
  all_goals rfl

theorem atot8159 : totK PA10K2 A10K2.u8159 = [0, 0, 0, 321051690767, 2102725480083, 4246215607186, 2928838191002, 500900764911, 13242594235, 0] := by
  rw [show A10K2.u8159 = KTree.node A10K2.t8168 (nat_lit 134049900) (nat_lit 5111782008) (nat_lit 0) A10K2.t8169 from rfl, totK_node, tot8168, tot8169]
  decide +kernel

theorem arows8160 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8160 = true := by
  rw [show A10K2.u8160 = KTree.node A10K2.t8170 (nat_lit 134063902) (nat_lit 11378213364) (nat_lit 0) A10K2.t8171 from rfl, allE_node, rows8170, irow8160, rows8171]
  all_goals rfl

theorem atot8160 : totK PA10K2 A10K2.u8160 = [0, 0, 0, 0, 916761908774, 3526126745950, 4075649303587, 1268019958619, 74624069451, 0] := by
  rw [show A10K2.u8160 = KTree.node A10K2.t8170 (nat_lit 134063902) (nat_lit 11378213364) (nat_lit 0) A10K2.t8171 from rfl, totK_node, tot8170, tot8171]
  decide +kernel

theorem arows8162 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8162 = true := by
  rw [show A10K2.u8162 = KTree.node A10K2.t8172 (nat_lit 134071520) (nat_lit 2375055151) (nat_lit 32) A10K2.t8173 from rfl, allE_node, rows8172, irow8162, rows8173]
  all_goals rfl

theorem atot8162 : totK PA10K2 A10K2.u8162 = [0, 0, 0, 0, 940216513409, 3268649136970, 3778748305380, 1603481091560, 235484071426, 6860445330] := by
  rw [show A10K2.u8162 = KTree.node A10K2.t8172 (nat_lit 134071520) (nat_lit 2375055151) (nat_lit 32) A10K2.t8173 from rfl, totK_node, tot8172, tot8173]
  decide +kernel

theorem arows8163 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8163 = true := by
  rw [show A10K2.u8163 = KTree.node A10K2.t8174 (nat_lit 134152265) (nat_lit 9594707706) (nat_lit 0) A10K2.t8175 from rfl, allE_node, rows8174, irow8163, rows8175]
  all_goals rfl

theorem atot8163 : totK PA10K2 A10K2.u8163 = [0, 0, 0, 711321896246, 2525555033707, 3273034765306, 2370794373303, 795344185693, 62331537917, 0] := by
  rw [show A10K2.u8163 = KTree.node A10K2.t8174 (nat_lit 134152265) (nat_lit 9594707706) (nat_lit 0) A10K2.t8175 from rfl, totK_node, tot8174, tot8175]
  decide +kernel

theorem arows8167 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8167 = true := by
  rw [show A10K2.u8167 = KTree.node A10K2.t8176 (nat_lit 134158337) (nat_lit 10498121125) (nat_lit 0) A10K2.t8177 from rfl, allE_node, rows8176, irow8167, rows8177]
  all_goals rfl

theorem atot8167 : totK PA10K2 A10K2.u8167 = [0, 0, 0, 340676889800, 2170554302293, 4145176280779, 2616884424468, 406416690534, 11694325420, 0] := by
  rw [show A10K2.u8167 = KTree.node A10K2.t8176 (nat_lit 134158337) (nat_lit 10498121125) (nat_lit 0) A10K2.t8177 from rfl, totK_node, tot8176, tot8177]
  decide +kernel

theorem arows8168 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8168 = true := by
  rw [show A10K2.u8168 = KTree.node A10K2.t8178 (nat_lit 134164403) (nat_lit 9302984323) (nat_lit 0) A10K2.t8179 from rfl, allE_node, rows8178, irow8168, rows8179]
  all_goals rfl

theorem atot8168 : totK PA10K2 A10K2.u8168 = [0, 0, 0, 464903275228, 2413158665866, 4046103957041, 2386885065759, 350073214354, 11918539728, 0] := by
  rw [show A10K2.u8168 = KTree.node A10K2.t8178 (nat_lit 134164403) (nat_lit 9302984323) (nat_lit 0) A10K2.t8179 from rfl, totK_node, tot8178, tot8179]
  decide +kernel

theorem arows8170 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8170 = true := by
  rw [show A10K2.u8170 = KTree.node A10K2.t8180 (nat_lit 134178197) (nat_lit 4777374898) (nat_lit 0) A10K2.t8181 from rfl, allE_node, rows8180, irow8170, rows8181]
  all_goals rfl

theorem atot8170 : totK PA10K2 A10K2.u8170 = [0, 0, 0, 890887868445, 3450351488030, 4092206808415, 1448112176404, 102349873967, 0, 0] := by
  rw [show A10K2.u8170 = KTree.node A10K2.t8180 (nat_lit 134178197) (nat_lit 4777374898) (nat_lit 0) A10K2.t8181 from rfl, totK_node, tot8180, tot8181]
  decide +kernel

theorem arows8171 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8171 = true := by
  rw [show A10K2.u8171 = KTree.node A10K2.t8182 (nat_lit 134182643) (nat_lit 8127202821) (nat_lit 0) A10K2.t8183 from rfl, allE_node, rows8182, irow8171, rows8183]
  all_goals rfl

theorem atot8171 : totK PA10K2 A10K2.u8171 = [0, 0, 0, 0, 1092523869459, 3790041156386, 3852324156470, 1027949844349, 62833682686, 0] := by
  rw [show A10K2.u8171 = KTree.node A10K2.t8182 (nat_lit 134182643) (nat_lit 8127202821) (nat_lit 0) A10K2.t8183 from rfl, totK_node, tot8182, tot8183]
  decide +kernel

theorem arows8174 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8174 = true := by
  rw [show A10K2.u8174 = KTree.node A10K2.t8184 (nat_lit 134188616) (nat_lit 13427451824) (nat_lit 0) A10K2.t8185 from rfl, allE_node, rows8184, irow8174, rows8185]
  all_goals rfl

theorem atot8174 : totK PA10K2 A10K2.u8174 = [0, 0, 0, 0, 544821805588, 2753468705386, 4206346323866, 1895268365462, 237813517898, 6318667960] := by
  rw [show A10K2.u8174 = KTree.node A10K2.t8184 (nat_lit 134188616) (nat_lit 13427451824) (nat_lit 0) A10K2.t8185 from rfl, totK_node, tot8184, tot8185]
  decide +kernel

theorem arows8175 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8175 = true := by
  rw [show A10K2.u8175 = KTree.node A10K2.t8186 (nat_lit 134196273) (nat_lit 9220537782) (nat_lit 0) A10K2.t8187 from rfl, allE_node, rows8186, irow8175, rows8187]
  all_goals rfl

theorem atot8175 : totK PA10K2 A10K2.u8175 = [0, 0, 0, 0, 754436196776, 3029658730015, 4076510119318, 1753023433972, 159616828142, 0] := by
  rw [show A10K2.u8175 = KTree.node A10K2.t8186 (nat_lit 134196273) (nat_lit 9220537782) (nat_lit 0) A10K2.t8187 from rfl, totK_node, tot8186, tot8187]
  decide +kernel

theorem arows8177 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8177 = true := by
  rw [show A10K2.u8177 = KTree.node A10K2.t8188 (nat_lit 134210369) (nat_lit 9087696848) (nat_lit 0) A10K2.t8189 from rfl, allE_node, rows8188, irow8177, rows8189]
  all_goals rfl

theorem atot8177 : totK PA10K2 A10K2.u8177 = [0, 0, 0, 0, 878740748981, 3374630846868, 3829696980866, 1499959047648, 194720579202, 6439430839] := by
  rw [show A10K2.u8177 = KTree.node A10K2.t8188 (nat_lit 134210369) (nat_lit 9087696848) (nat_lit 0) A10K2.t8189 from rfl, totK_node, tot8188, tot8189]
  decide +kernel

theorem arows8178 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8178 = true := by
  rw [show A10K2.u8178 = KTree.node A10K2.t8190 (nat_lit 134215046) (nat_lit 15827254995) (nat_lit 0) A10K2.t8191 from rfl, allE_node, rows8190, irow8178, rows8191]
  all_goals rfl

theorem atot8178 : totK PA10K2 A10K2.u8178 = [0, 0, 0, 0, 0, 1152394427139, 3885958710940, 3663405847181, 961189328672, 61018386929] := by
  rw [show A10K2.u8178 = KTree.node A10K2.t8190 (nat_lit 134215046) (nat_lit 15827254995) (nat_lit 0) A10K2.t8191 from rfl, totK_node, tot8190, tot8191]
  decide +kernel

theorem arows2 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2 = true := by
  rw [show A10K2.u2 = KTree.node A10K2.u0 (nat_lit 4456) (nat_lit 9719076119) (nat_lit 0) A10K2.u1 from rfl, allE_node, arows0, irow2, arows1]
  all_goals rfl

theorem atot2 : totK PA10K2 A10K2.u2 = [1315311876802, 5575133523772, 7802973546721, 4005282468241, 660874445441, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u2 = KTree.node A10K2.u0 (nat_lit 4456) (nat_lit 9719076119) (nat_lit 0) A10K2.u1 from rfl, totK_node, atot0, atot1]
  decide +kernel

theorem arows5 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5 = true := by
  rw [show A10K2.u5 = KTree.node A10K2.u3 (nat_lit 25024) (nat_lit 15203328423) (nat_lit 0) A10K2.u4 from rfl, allE_node, arows3, irow5, arows4]
  all_goals rfl

theorem atot5 : totK PA10K2 A10K2.u5 = [1064723519677, 5187714416618, 8172218295857, 4311572886821, 632490049054, 13207830636, 0, 0, 0, 0] := by
  rw [show A10K2.u5 = KTree.node A10K2.u3 (nat_lit 25024) (nat_lit 15203328423) (nat_lit 0) A10K2.u4 from rfl, totK_node, atot3, atot4]
  decide +kernel

theorem arows9 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u9 = true := by
  rw [show A10K2.u9 = KTree.node A10K2.u7 (nat_lit 35844) (nat_lit 10625901368) (nat_lit 0) A10K2.u8 from rfl, allE_node, arows7, irow9, arows8]
  all_goals rfl

theorem atot9 : totK PA10K2 A10K2.u9 = [0, 1292219419776, 5577180701079, 7925016795948, 3856061422019, 635608075274, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u9 = KTree.node A10K2.u7 (nat_lit 35844) (nat_lit 10625901368) (nat_lit 0) A10K2.u8 from rfl, totK_node, atot7, atot8]
  decide +kernel

theorem arows12 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u12 = true := by
  rw [show A10K2.u12 = KTree.node A10K2.u10 (nat_lit 55469) (nat_lit 6561767260) (nat_lit 0) A10K2.u11 from rfl, allE_node, arows10, irow12, arows11]
  all_goals rfl

theorem atot12 : totK PA10K2 A10K2.u12 = [115575618874, 1636214677357, 6147539678944, 7884618338074, 3055497273501, 306773984204, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u12 = KTree.node A10K2.u10 (nat_lit 55469) (nat_lit 6561767260) (nat_lit 0) A10K2.u11 from rfl, totK_node, atot10, atot11]
  decide +kernel

theorem arows17 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u17 = true := by
  rw [show A10K2.u17 = KTree.node A10K2.u15 (nat_lit 135962) (nat_lit 5167980615) (nat_lit 0) A10K2.u16 from rfl, allE_node, arows15, irow17, arows16]
  all_goals rfl

theorem atot17 : totK PA10K2 A10K2.u17 = [1110885087375, 5178240132953, 7856062033539, 4262457329264, 757311191709, 46002817009, 0, 0, 0, 0] := by
  rw [show A10K2.u17 = KTree.node A10K2.u15 (nat_lit 135962) (nat_lit 5167980615) (nat_lit 0) A10K2.u16 from rfl, totK_node, atot15, atot16]
  decide +kernel

theorem arows20 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u20 = true := by
  rw [show A10K2.u20 = KTree.node A10K2.u18 (nat_lit 149866) (nat_lit 9839619679) (nat_lit 0) A10K2.u19 from rfl, allE_node, arows18, irow20, arows19]
  all_goals rfl

theorem atot20 : totK PA10K2 A10K2.u20 = [774098640671, 4250269408012, 7543355355577, 4893283956673, 1003789114140, 48585361399, 0, 0, 0, 0] := by
  rw [show A10K2.u20 = KTree.node A10K2.u18 (nat_lit 149866) (nat_lit 9839619679) (nat_lit 0) A10K2.u19 from rfl, totK_node, atot18, atot19]
  decide +kernel

theorem arows24 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u24 = true := by
  rw [show A10K2.u24 = KTree.node A10K2.u22 (nat_lit 180608) (nat_lit 15058423936) (nat_lit 0) A10K2.u23 from rfl, allE_node, arows22, irow24, arows23]
  all_goals rfl

theorem atot24 : totK PA10K2 A10K2.u24 = [0, 1581023159589, 6569749425079, 7758191363402, 2435303127740, 173708733312, 0, 0, 0, 0] := by
  rw [show A10K2.u24 = KTree.node A10K2.u22 (nat_lit 180608) (nat_lit 15058423936) (nat_lit 0) A10K2.u23 from rfl, totK_node, atot22, atot23]
  decide +kernel

theorem arows27 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u27 = true := by
  rw [show A10K2.u27 = KTree.node A10K2.u25 (nat_lit 200641) (nat_lit 8997799152) (nat_lit 0) A10K2.u26 from rfl, allE_node, arows25, irow27, arows26]
  all_goals rfl

theorem atot27 : totK PA10K2 A10K2.u27 = [1292095572706, 5208035420955, 7229645301431, 4383657491818, 1377488470261, 218763650657, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u27 = KTree.node A10K2.u25 (nat_lit 200641) (nat_lit 8997799152) (nat_lit 0) A10K2.u26 from rfl, totK_node, atot25, atot26]
  decide +kernel

theorem arows33 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u33 = true := by
  rw [show A10K2.u33 = KTree.node A10K2.u31 (nat_lit 223153) (nat_lit 7628858159) (nat_lit 0) A10K2.u32 from rfl, allE_node, arows31, irow33, arows32]
  all_goals rfl

theorem atot33 : totK PA10K2 A10K2.u33 = [836280282984, 4732284906993, 8449305656421, 5172225094463, 850211408118, 28470656162, 0, 0, 0, 0] := by
  rw [show A10K2.u33 = KTree.node A10K2.u31 (nat_lit 223153) (nat_lit 7628858159) (nat_lit 0) A10K2.u32 from rfl, totK_node, atot31, atot32]
  decide +kernel

theorem arows36 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u36 = true := by
  rw [show A10K2.u36 = KTree.node A10K2.u34 (nat_lit 233431) (nat_lit 14217301965) (nat_lit 0) A10K2.u35 from rfl, allE_node, arows34, irow36, arows35]
  all_goals rfl

theorem atot36 : totK PA10K2 A10K2.u36 = [0, 1290913363296, 5879272704601, 8441377728705, 3843202779664, 443708874646, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u36 = KTree.node A10K2.u34 (nat_lit 233431) (nat_lit 14217301965) (nat_lit 0) A10K2.u35 from rfl, totK_node, atot34, atot35]
  decide +kernel

theorem arows40 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u40 = true := by
  rw [show A10K2.u40 = KTree.node A10K2.u38 (nat_lit 257421) (nat_lit 3588483070) (nat_lit 0) A10K2.u39 from rfl, allE_node, arows38, irow40, arows39]
  all_goals rfl

theorem atot40 : totK PA10K2 A10K2.u40 = [0, 835479949481, 4412711189784, 8014245869343, 5477982579640, 1044307676047, 30846741173, 0, 0, 0] := by
  rw [show A10K2.u40 = KTree.node A10K2.u38 (nat_lit 257421) (nat_lit 3588483070) (nat_lit 0) A10K2.u39 from rfl, totK_node, atot38, atot39]
  decide +kernel

theorem arows43 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u43 = true := by
  rw [show A10K2.u43 = KTree.node A10K2.u41 (nat_lit 266508) (nat_lit 11846322472) (nat_lit 0) A10K2.u42 from rfl, allE_node, arows41, irow43, arows42]
  all_goals rfl

theorem atot43 : totK PA10K2 A10K2.u43 = [0, 1312429190084, 5450228460147, 7605186276723, 4032289375873, 850997369390, 68142084271, 0, 0, 0] := by
  rw [show A10K2.u43 = KTree.node A10K2.u41 (nat_lit 266508) (nat_lit 11846322472) (nat_lit 0) A10K2.u42 from rfl, totK_node, atot41, atot42]
  decide +kernel

theorem arows48 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u48 = true := by
  rw [show A10K2.u48 = KTree.node A10K2.u46 (nat_lit 287180) (nat_lit 6954830048) (nat_lit 0) A10K2.u47 from rfl, allE_node, arows46, irow48, arows47]
  all_goals rfl

theorem atot48 : totK PA10K2 A10K2.u48 = [0, 1063445225170, 5283295990322, 8239700156275, 4167277079059, 540131505057, 12558367923, 0, 0, 0] := by
  rw [show A10K2.u48 = KTree.node A10K2.u46 (nat_lit 287180) (nat_lit 6954830048) (nat_lit 0) A10K2.u47 from rfl, totK_node, atot46, atot47]
  decide +kernel

theorem arows51 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u51 = true := by
  rw [show A10K2.u51 = KTree.node A10K2.u49 (nat_lit 298425) (nat_lit 7083371331) (nat_lit 0) A10K2.u50 from rfl, allE_node, arows49, irow51, arows50]
  all_goals rfl

theorem atot51 : totK PA10K2 A10K2.u51 = [0, 0, 1456640324854, 5881213721084, 7534137314206, 3504819995407, 603836708998, 30605747850, 0, 0] := by
  rw [show A10K2.u51 = KTree.node A10K2.u49 (nat_lit 298425) (nat_lit 7083371331) (nat_lit 0) A10K2.u50 from rfl, totK_node, atot49, atot50]
  decide +kernel

theorem arows55 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u55 = true := by
  rw [show A10K2.u55 = KTree.node A10K2.u53 (nat_lit 318253) (nat_lit 6480117215) (nat_lit 0) A10K2.u54 from rfl, allE_node, arows53, irow55, arows54]
  all_goals rfl

theorem atot55 : totK PA10K2 A10K2.u55 = [0, 412800395519, 2476634645747, 6318854082102, 6967314949387, 2507809320281, 271643173512, 5528811039, 0, 0] := by
  rw [show A10K2.u55 = KTree.node A10K2.u53 (nat_lit 318253) (nat_lit 6480117215) (nat_lit 0) A10K2.u54 from rfl, totK_node, atot53, atot54]
  decide +kernel

theorem arows58 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u58 = true := by
  rw [show A10K2.u58 = KTree.node A10K2.u56 (nat_lit 400197) (nat_lit 6486569614) (nat_lit 0) A10K2.u57 from rfl, allE_node, arows56, irow58, arows57]
  all_goals rfl

theorem atot58 : totK PA10K2 A10K2.u58 = [0, 999536686008, 4780968408335, 7724773200595, 4508067152591, 798318339251, 36865889447, 0, 0, 0] := by
  rw [show A10K2.u58 = KTree.node A10K2.u56 (nat_lit 400197) (nat_lit 6486569614) (nat_lit 0) A10K2.u57 from rfl, totK_node, atot56, atot57]
  decide +kernel

theorem arows65 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u65 = true := by
  rw [show A10K2.u65 = KTree.node A10K2.u63 (nat_lit 415752) (nat_lit 14111335316) (nat_lit 0) A10K2.u64 from rfl, allE_node, arows63, irow65, arows64]
  all_goals rfl

theorem atot65 : totK PA10K2 A10K2.u65 = [0, 587096145623, 3965819179702, 7811939198416, 5207811726114, 1011407191141, 44905858284, 0, 0, 0] := by
  rw [show A10K2.u65 = KTree.node A10K2.u63 (nat_lit 415752) (nat_lit 14111335316) (nat_lit 0) A10K2.u64 from rfl, totK_node, atot63, atot64]
  decide +kernel

theorem arows68 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u68 = true := by
  rw [show A10K2.u68 = KTree.node A10K2.u66 (nat_lit 444757) (nat_lit 6980450443) (nat_lit 0) A10K2.u67 from rfl, allE_node, arows66, irow68, arows67]
  all_goals rfl

theorem atot68 : totK PA10K2 A10K2.u68 = [0, 509695482927, 2818027578422, 6419117028289, 6373498301875, 2143634031880, 229167355618, 5676195732, 0, 0] := by
  rw [show A10K2.u68 = KTree.node A10K2.u66 (nat_lit 444757) (nat_lit 6980450443) (nat_lit 0) A10K2.u67 from rfl, totK_node, atot66, atot67]
  decide +kernel

theorem arows72 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u72 = true := by
  rw [show A10K2.u72 = KTree.node A10K2.u70 (nat_lit 468145) (nat_lit 4923997468) (nat_lit 0) A10K2.u71 from rfl, allE_node, arows70, irow72, arows71]
  all_goals rfl

theorem atot72 : totK PA10K2 A10K2.u72 = [0, 1065997115591, 5247292245754, 8402537973936, 4596705666176, 767891836129, 32464529119, 0, 0, 0] := by
  rw [show A10K2.u72 = KTree.node A10K2.u70 (nat_lit 468145) (nat_lit 4923997468) (nat_lit 0) A10K2.u71 from rfl, totK_node, atot70, atot71]
  decide +kernel

theorem arows75 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u75 = true := by
  rw [show A10K2.u75 = KTree.node A10K2.u73 (nat_lit 488841) (nat_lit 7965281208) (nat_lit 0) A10K2.u74 from rfl, allE_node, arows73, irow75, arows74]
  all_goals rfl

theorem atot75 : totK PA10K2 A10K2.u75 = [583967476257, 2558134462174, 4913594014949, 6244684954390, 4285520058417, 1045780911075, 62368562949, 0, 0, 0] := by
  rw [show A10K2.u75 = KTree.node A10K2.u73 (nat_lit 488841) (nat_lit 7965281208) (nat_lit 0) A10K2.u74 from rfl, totK_node, atot73, atot74]
  decide +kernel

theorem arows80 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u80 = true := by
  rw [show A10K2.u80 = KTree.node A10K2.u78 (nat_lit 1056178) (nat_lit 12467972683) (nat_lit 0) A10K2.u79 from rfl, allE_node, arows78, irow80, arows79]
  all_goals rfl

theorem atot80 : totK PA10K2 A10K2.u80 = [1017267642606, 5020105265130, 7998993906512, 4334755094646, 690599651892, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u80 = KTree.node A10K2.u78 (nat_lit 1056178) (nat_lit 12467972683) (nat_lit 0) A10K2.u79 from rfl, totK_node, atot78, atot79]
  decide +kernel

theorem arows83 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u83 = true := by
  rw [show A10K2.u83 = KTree.node A10K2.u81 (nat_lit 1077319) (nat_lit 11122647682) (nat_lit 0) A10K2.u82 from rfl, allE_node, arows81, irow83, arows82]
  all_goals rfl

theorem atot83 : totK PA10K2 A10K2.u83 = [590238606807, 3728787694795, 7837277472479, 5994822092831, 1444456902721, 87191068714, 0, 0, 0, 0] := by
  rw [show A10K2.u83 = KTree.node A10K2.u81 (nat_lit 1077319) (nat_lit 11122647682) (nat_lit 0) A10K2.u82 from rfl, totK_node, atot81, atot82]
  decide +kernel

theorem arows87 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u87 = true := by
  rw [show A10K2.u87 = KTree.node A10K2.u85 (nat_lit 1088905) (nat_lit 8696006851) (nat_lit 0) A10K2.u86 from rfl, allE_node, arows85, irow87, arows86]
  all_goals rfl

theorem atot87 : totK PA10K2 A10K2.u87 = [0, 1015304901283, 5203741347525, 8089313850053, 3948560780979, 626612387376, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u87 = KTree.node A10K2.u85 (nat_lit 1088905) (nat_lit 8696006851) (nat_lit 0) A10K2.u86 from rfl, totK_node, atot85, atot86]
  decide +kernel

theorem arows90 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u90 = true := by
  rw [show A10K2.u90 = KTree.node A10K2.u88 (nat_lit 1123741) (nat_lit 5211181181) (nat_lit 0) A10K2.u89 from rfl, allE_node, arows88, irow90, arows89]
  all_goals rfl

theorem atot90 : totK PA10K2 A10K2.u90 = [664492635903, 3344682933134, 6674183245882, 6197879021403, 2271767127947, 260973457281, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u90 = KTree.node A10K2.u88 (nat_lit 1123741) (nat_lit 5211181181) (nat_lit 0) A10K2.u89 from rfl, totK_node, atot88, atot89]
  decide +kernel

theorem arows96 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u96 = true := by
  rw [show A10K2.u96 = KTree.node A10K2.u94 (nat_lit 1136708) (nat_lit 11704802170) (nat_lit 0) A10K2.u95 from rfl, allE_node, arows94, irow96, arows95]
  all_goals rfl

theorem atot96 : totK PA10K2 A10K2.u96 = [637411369818, 3822274289148, 7354844939298, 5399188687487, 1593010372392, 202437743460, 15171143123, 0, 0, 0] := by
  rw [show A10K2.u96 = KTree.node A10K2.u94 (nat_lit 1136708) (nat_lit 11704802170) (nat_lit 0) A10K2.u95 from rfl, totK_node, atot94, atot95]
  decide +kernel

theorem arows99 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u99 = true := by
  rw [show A10K2.u99 = KTree.node A10K2.u97 (nat_lit 1166088) (nat_lit 11686615978) (nat_lit 0) A10K2.u98 from rfl, allE_node, arows97, irow99, arows98]
  all_goals rfl

theorem atot99 : totK PA10K2 A10K2.u99 = [580977587835, 2514732175625, 5229723823887, 6402705554217, 3387399934458, 579528332948, 22032916775, 0, 0, 0] := by
  rw [show A10K2.u99 = KTree.node A10K2.u97 (nat_lit 1166088) (nat_lit 11686615978) (nat_lit 0) A10K2.u98 from rfl, totK_node, atot97, atot98]
  decide +kernel

theorem arows103 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u103 = true := by
  rw [show A10K2.u103 = KTree.node A10K2.u101 (nat_lit 1189036) (nat_lit 12636768037) (nat_lit 0) A10K2.u102 from rfl, allE_node, arows101, irow103, arows102]
  all_goals rfl

theorem atot103 : totK PA10K2 A10K2.u103 = [770234795241, 4407878989990, 7921064710767, 4885824084591, 975760091647, 56566207178, 0, 0, 0, 0] := by
  rw [show A10K2.u103 = KTree.node A10K2.u101 (nat_lit 1189036) (nat_lit 12636768037) (nat_lit 0) A10K2.u102 from rfl, totK_node, atot101, atot102]
  decide +kernel

theorem arows106 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u106 = true := by
  rw [show A10K2.u106 = KTree.node A10K2.u104 (nat_lit 1200183) (nat_lit 11136119746) (nat_lit 0) A10K2.u105 from rfl, allE_node, arows104, irow106, arows105]
  all_goals rfl

theorem atot106 : totK PA10K2 A10K2.u106 = [821967029087, 4447212068663, 7764884553215, 4780654611808, 881110572377, 38021971230, 0, 0, 0, 0] := by
  rw [show A10K2.u106 = KTree.node A10K2.u104 (nat_lit 1200183) (nat_lit 11136119746) (nat_lit 0) A10K2.u105 from rfl, totK_node, atot104, atot105]
  decide +kernel

theorem arows111 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u111 = true := by
  rw [show A10K2.u111 = KTree.node A10K2.u109 (nat_lit 1229162) (nat_lit 9249972780) (nat_lit 0) A10K2.u110 from rfl, allE_node, arows109, irow111, arows110]
  all_goals rfl

theorem atot111 : totK PA10K2 A10K2.u111 = [0, 1585674655263, 6623007842497, 7929286037238, 2453833914331, 161265129909, 0, 0, 0, 0] := by
  rw [show A10K2.u111 = KTree.node A10K2.u109 (nat_lit 1229162) (nat_lit 9249972780) (nat_lit 0) A10K2.u110 from rfl, totK_node, atot109, atot110]
  decide +kernel

theorem arows114 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u114 = true := by
  rw [show A10K2.u114 = KTree.node A10K2.u112 (nat_lit 1314363) (nat_lit 4545124752) (nat_lit 0) A10K2.u113 from rfl, allE_node, arows112, irow114, arows113]
  all_goals rfl

theorem atot114 : totK PA10K2 A10K2.u114 = [0, 1130031047312, 5005214635226, 7725100590098, 4394350065704, 807286985849, 37172849495, 0, 0, 0] := by
  rw [show A10K2.u114 = KTree.node A10K2.u112 (nat_lit 1314363) (nat_lit 4545124752) (nat_lit 0) A10K2.u113 from rfl, totK_node, atot112, atot113]
  decide +kernel

theorem arows118 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u118 = true := by
  rw [show A10K2.u118 = KTree.node A10K2.u116 (nat_lit 1333760) (nat_lit 14966411464) (nat_lit 0) A10K2.u117 from rfl, allE_node, arows116, irow118, arows117]
  all_goals rfl

theorem atot118 : totK PA10K2 A10K2.u118 = [0, 1061442678358, 5186667347175, 8124699480240, 4267592553856, 614402504722, 13207830636, 0, 0, 0] := by
  rw [show A10K2.u118 = KTree.node A10K2.u116 (nat_lit 1333760) (nat_lit 14966411464) (nat_lit 0) A10K2.u117 from rfl, totK_node, atot116, atot117]
  decide +kernel

theorem arows121 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u121 = true := by
  rw [show A10K2.u121 = KTree.node A10K2.u119 (nat_lit 1390636) (nat_lit 12993419245) (nat_lit 0) A10K2.u120 from rfl, allE_node, arows119, irow121, arows120]
  all_goals rfl

theorem atot121 : totK PA10K2 A10K2.u121 = [0, 1299274360047, 5556453687430, 7740303649283, 3902362243239, 653381473448, 31452573850, 0, 0, 0] := by
  rw [show A10K2.u121 = KTree.node A10K2.u119 (nat_lit 1390636) (nat_lit 12993419245) (nat_lit 0) A10K2.u120 from rfl, totK_node, atot119, atot120]
  decide +kernel

theorem arows129 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u129 = true := by
  rw [show A10K2.u129 = KTree.node A10K2.u127 (nat_lit 1444514) (nat_lit 13436388175) (nat_lit 0) A10K2.u128 from rfl, allE_node, arows127, irow129, arows128]
  all_goals rfl

theorem atot129 : totK PA10K2 A10K2.u129 = [0, 969558303174, 4730232792734, 7871962149128, 4535394196418, 761234520929, 36429366174, 0, 0, 0] := by
  rw [show A10K2.u129 = KTree.node A10K2.u127 (nat_lit 1444514) (nat_lit 13436388175) (nat_lit 0) A10K2.u128 from rfl, totK_node, atot127, atot128]
  decide +kernel

theorem arows132 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u132 = true := by
  rw [show A10K2.u132 = KTree.node A10K2.u130 (nat_lit 1457301) (nat_lit 5908245987) (nat_lit 0) A10K2.u131 from rfl, allE_node, arows130, irow132, arows131]
  all_goals rfl

theorem atot132 : totK PA10K2 A10K2.u132 = [0, 1201014161680, 5381647591631, 7656506094978, 3730605825689, 593182314724, 31003444686, 0, 0, 0] := by
  rw [show A10K2.u132 = KTree.node A10K2.u130 (nat_lit 1457301) (nat_lit 5908245987) (nat_lit 0) A10K2.u131 from rfl, totK_node, atot130, atot131]
  decide +kernel

theorem arows136 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u136 = true := by
  rw [show A10K2.u136 = KTree.node A10K2.u134 (nat_lit 1477477) (nat_lit 7244901681) (nat_lit 0) A10K2.u135 from rfl, allE_node, arows134, irow136, arows135]
  all_goals rfl

theorem atot136 : totK PA10K2 A10K2.u136 = [0, 0, 2302676366059, 7646561243931, 6830260623265, 1585524514260, 93893887517, 0, 0, 0] := by
  rw [show A10K2.u136 = KTree.node A10K2.u134 (nat_lit 1477477) (nat_lit 7244901681) (nat_lit 0) A10K2.u135 from rfl, totK_node, atot134, atot135]
  decide +kernel

theorem arows139 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u139 = true := by
  rw [show A10K2.u139 = KTree.node A10K2.u137 (nat_lit 1572865) (nat_lit 10630474206) (nat_lit 0) A10K2.u138 from rfl, allE_node, arows137, irow139, arows138]
  all_goals rfl

theorem atot139 : totK PA10K2 A10K2.u139 = [844183794776, 3386164465852, 4459749738207, 3859217756306, 4036146081567, 1916008859231, 291068676346, 6354482628, 0, 0] := by
  rw [show A10K2.u139 = KTree.node A10K2.u137 (nat_lit 1572865) (nat_lit 10630474206) (nat_lit 0) A10K2.u138 from rfl, totK_node, atot137, atot138]
  decide +kernel

theorem arows144 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u144 = true := by
  rw [show A10K2.u144 = KTree.node A10K2.u142 (nat_lit 1591653) (nat_lit 7356623569) (nat_lit 0) A10K2.u143 from rfl, allE_node, arows142, irow144, arows143]
  all_goals rfl

theorem atot144 : totK PA10K2 A10K2.u144 = [1050007150656, 4933434688320, 7857506809045, 4558617515156, 838047938766, 37186156514, 0, 0, 0, 0] := by
  rw [show A10K2.u144 = KTree.node A10K2.u142 (nat_lit 1591653) (nat_lit 7356623569) (nat_lit 0) A10K2.u143 from rfl, totK_node, atot142, atot143]
  decide +kernel

theorem arows147 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u147 = true := by
  rw [show A10K2.u147 = KTree.node A10K2.u145 (nat_lit 1605176) (nat_lit 14204811161) (nat_lit 0) A10K2.u146 from rfl, allE_node, arows145, irow147, arows146]
  all_goals rfl

theorem atot147 : totK PA10K2 A10K2.u147 = [319203061299, 2829979741296, 7539894097170, 7211393197866, 1986245054761, 123195634356, 0, 0, 0, 0] := by
  rw [show A10K2.u147 = KTree.node A10K2.u145 (nat_lit 1605176) (nat_lit 14204811161) (nat_lit 0) A10K2.u146 from rfl, totK_node, atot145, atot146]
  decide +kernel

theorem arows151 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u151 = true := by
  rw [show A10K2.u151 = KTree.node A10K2.u149 (nat_lit 1624213) (nat_lit 6840212376) (nat_lit 0) A10K2.u150 from rfl, allE_node, arows149, irow151, arows150]
  all_goals rfl

theorem atot151 : totK PA10K2 A10K2.u151 = [0, 1047501856782, 5012194374012, 7820324300107, 4272992638088, 759113086032, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u151 = KTree.node A10K2.u149 (nat_lit 1624213) (nat_lit 6840212376) (nat_lit 0) A10K2.u150 from rfl, totK_node, atot149, atot150]
  decide +kernel

theorem arows154 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u154 = true := by
  rw [show A10K2.u154 = KTree.node A10K2.u152 (nat_lit 1650678) (nat_lit 16691704329) (nat_lit 0) A10K2.u153 from rfl, allE_node, arows152, irow154, arows153]
  all_goals rfl

theorem atot154 : totK PA10K2 A10K2.u154 = [1267590511789, 5297681029582, 7771439666217, 4840502238094, 1211829302031, 83285703060, 0, 0, 0, 0] := by
  rw [show A10K2.u154 = KTree.node A10K2.u152 (nat_lit 1650678) (nat_lit 16691704329) (nat_lit 0) A10K2.u153 from rfl, totK_node, atot152, atot153]
  decide +kernel

theorem arows160 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u160 = true := by
  rw [show A10K2.u160 = KTree.node A10K2.u158 (nat_lit 1671103) (nat_lit 14276822153) (nat_lit 0) A10K2.u159 from rfl, allE_node, arows158, irow160, arows159]
  all_goals rfl

theorem atot160 : totK PA10K2 A10K2.u160 = [121146523123, 2105574848522, 6774965074020, 7641730372507, 3124732323330, 465419144352, 25565504801, 0, 0, 0] := by
  rw [show A10K2.u160 = KTree.node A10K2.u158 (nat_lit 1671103) (nat_lit 14276822153) (nat_lit 0) A10K2.u159 from rfl, totK_node, atot158, atot159]
  decide +kernel

theorem arows163 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u163 = true := by
  rw [show A10K2.u163 = KTree.node A10K2.u161 (nat_lit 1769928) (nat_lit 14209543142) (nat_lit 0) A10K2.u162 from rfl, allE_node, arows161, irow163, arows162]
  all_goals rfl

theorem atot163 : totK PA10K2 A10K2.u163 = [781939065379, 4058875934724, 7488629250917, 5835600647635, 1691415516182, 126487116347, 0, 0, 0, 0] := by
  rw [show A10K2.u163 = KTree.node A10K2.u161 (nat_lit 1769928) (nat_lit 14209543142) (nat_lit 0) A10K2.u162 from rfl, totK_node, atot161, atot162]
  decide +kernel

theorem arows167 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u167 = true := by
  rw [show A10K2.u167 = KTree.node A10K2.u165 (nat_lit 1783122) (nat_lit 15080118258) (nat_lit 0) A10K2.u166 from rfl, allE_node, arows165, irow167, arows166]
  all_goals rfl

theorem atot167 : totK PA10K2 A10K2.u167 = [1275180868120, 5598022630471, 8123581642663, 4266536906535, 658644179337, 25199378929, 0, 0, 0, 0] := by
  rw [show A10K2.u167 = KTree.node A10K2.u165 (nat_lit 1783122) (nat_lit 15080118258) (nat_lit 0) A10K2.u166 from rfl, totK_node, atot165, atot166]
  decide +kernel

theorem arows170 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u170 = true := by
  rw [show A10K2.u170 = KTree.node A10K2.u168 (nat_lit 1801760) (nat_lit 13354457834) (nat_lit 0) A10K2.u169 from rfl, allE_node, arows168, irow170, arows169]
  all_goals rfl

theorem atot170 : totK PA10K2 A10K2.u170 = [226625864075, 2589168495660, 7447421257700, 7352895855783, 2177728600441, 144550282763, 0, 0, 0, 0] := by
  rw [show A10K2.u170 = KTree.node A10K2.u168 (nat_lit 1801760) (nat_lit 13354457834) (nat_lit 0) A10K2.u169 from rfl, totK_node, atot168, atot169]
  decide +kernel

theorem arows175 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u175 = true := by
  rw [show A10K2.u175 = KTree.node A10K2.u173 (nat_lit 1814129) (nat_lit 7695224683) (nat_lit 0) A10K2.u174 from rfl, allE_node, arows173, irow175, arows174]
  all_goals rfl

theorem atot175 : totK PA10K2 A10K2.u175 = [0, 1169544243701, 5438508171011, 8220782842667, 4350836444516, 631541248246, 13951953716, 0, 0, 0] := by
  rw [show A10K2.u175 = KTree.node A10K2.u173 (nat_lit 1814129) (nat_lit 7695224683) (nat_lit 0) A10K2.u174 from rfl, totK_node, atot173, atot174]
  decide +kernel

theorem arows178 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u178 = true := by
  rw [show A10K2.u178 = KTree.node A10K2.u176 (nat_lit 1834156) (nat_lit 4682220454) (nat_lit 0) A10K2.u177 from rfl, allE_node, arows176, irow178, arows177]
  all_goals rfl

theorem atot178 : totK PA10K2 A10K2.u178 = [0, 1174194254189, 5086267754993, 7645554470468, 4634426997071, 1012451204287, 61110126106, 0, 0, 0] := by
  rw [show A10K2.u178 = KTree.node A10K2.u176 (nat_lit 1834156) (nat_lit 4682220454) (nat_lit 0) A10K2.u177 from rfl, totK_node, atot176, atot177]
  decide +kernel

theorem arows182 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u182 = true := by
  rw [show A10K2.u182 = KTree.node A10K2.u180 (nat_lit 1851913) (nat_lit 9779692840) (nat_lit 0) A10K2.u181 from rfl, allE_node, arows180, irow182, arows181]
  all_goals rfl

theorem atot182 : totK PA10K2 A10K2.u182 = [0, 848859785104, 4529143521928, 8000035122447, 4842381016341, 841226899384, 36485460093, 0, 0, 0] := by
  rw [show A10K2.u182 = KTree.node A10K2.u180 (nat_lit 1851913) (nat_lit 9779692840) (nat_lit 0) A10K2.u181 from rfl, totK_node, atot180, atot181]
  decide +kernel

theorem arows185 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u185 = true := by
  rw [show A10K2.u185 = KTree.node A10K2.u183 (nat_lit 1865392) (nat_lit 9943836900) (nat_lit 0) A10K2.u184 from rfl, allE_node, arows183, irow185, arows184]
  all_goals rfl

theorem atot185 : totK PA10K2 A10K2.u185 = [0, 520350426851, 3562811435052, 7806557904495, 6358571727312, 1575016872819, 93464514795, 0, 0, 0] := by
  rw [show A10K2.u185 = KTree.node A10K2.u183 (nat_lit 1865392) (nat_lit 9943836900) (nat_lit 0) A10K2.u184 from rfl, totK_node, atot183, atot184]
  decide +kernel

theorem arows192 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u192 = true := by
  rw [show A10K2.u192 = KTree.node A10K2.u190 (nat_lit 1885036) (nat_lit 11348012497) (nat_lit 0) A10K2.u191 from rfl, allE_node, arows190, irow192, arows191]
  all_goals rfl

theorem atot192 : totK PA10K2 A10K2.u192 = [0, 0, 1536718608616, 6467907335684, 8151457471885, 3082701662056, 339837168804, 7007974415, 0, 0] := by
  rw [show A10K2.u192 = KTree.node A10K2.u190 (nat_lit 1885036) (nat_lit 11348012497) (nat_lit 0) A10K2.u191 from rfl, totK_node, atot190, atot191]
  decide +kernel

theorem arows195 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u195 = true := by
  rw [show A10K2.u195 = KTree.node A10K2.u193 (nat_lit 1915977) (nat_lit 6153328429) (nat_lit 0) A10K2.u194 from rfl, allE_node, arows193, irow195, arows194]
  all_goals rfl

theorem atot195 : totK PA10K2 A10K2.u195 = [0, 1386739416170, 5840584796198, 8122768092674, 4180880212511, 819385870399, 63355047008, 0, 0, 0] := by
  rw [show A10K2.u195 = KTree.node A10K2.u193 (nat_lit 1915977) (nat_lit 6153328429) (nat_lit 0) A10K2.u194 from rfl, totK_node, atot193, atot194]
  decide +kernel

theorem arows199 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u199 = true := by
  rw [show A10K2.u199 = KTree.node A10K2.u197 (nat_lit 1943487) (nat_lit 13828888516) (nat_lit 0) A10K2.u198 from rfl, allE_node, arows197, irow199, arows198]
  all_goals rfl

theorem atot199 : totK PA10K2 A10K2.u199 = [0, 0, 1683459837189, 6628277753618, 8214638570571, 3342086567981, 387415300118, 7151180950, 0, 0] := by
  rw [show A10K2.u199 = KTree.node A10K2.u197 (nat_lit 1943487) (nat_lit 13828888516) (nat_lit 0) A10K2.u198 from rfl, totK_node, atot197, atot198]
  decide +kernel

theorem arows202 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u202 = true := by
  rw [show A10K2.u202 = KTree.node A10K2.u200 (nat_lit 2034806) (nat_lit 16190745451) (nat_lit 0) A10K2.u201 from rfl, allE_node, arows200, irow202, arows201]
  all_goals rfl

theorem atot202 : totK PA10K2 A10K2.u202 = [0, 1036882262728, 4575063920195, 7509708011216, 5300977187881, 1321836889033, 74623879111, 0, 0, 0] := by
  rw [show A10K2.u202 = KTree.node A10K2.u200 (nat_lit 2034806) (nat_lit 16190745451) (nat_lit 0) A10K2.u201 from rfl, totK_node, atot200, atot201]
  decide +kernel

theorem arows207 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u207 = true := by
  rw [show A10K2.u207 = KTree.node A10K2.u205 (nat_lit 2056225) (nat_lit 10077694148) (nat_lit 0) A10K2.u206 from rfl, allE_node, arows205, irow207, arows206]
  all_goals rfl

theorem atot207 : totK PA10K2 A10K2.u207 = [0, 1245373267684, 5766424135273, 8380715635908, 4036506300522, 533445010495, 12219140272, 0, 0, 0] := by
  rw [show A10K2.u207 = KTree.node A10K2.u205 (nat_lit 2056225) (nat_lit 10077694148) (nat_lit 0) A10K2.u206 from rfl, totK_node, atot205, atot206]
  decide +kernel

theorem arows210 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u210 = true := by
  rw [show A10K2.u210 = KTree.node A10K2.u208 (nat_lit 2065236) (nat_lit 5147766367) (nat_lit 0) A10K2.u209 from rfl, allE_node, arows208, irow210, arows209]
  all_goals rfl

theorem atot210 : totK PA10K2 A10K2.u210 = [0, 0, 1478176042790, 6254432176820, 8314021284532, 3368917442142, 347477512128, 6318667960, 0, 0] := by
  rw [show A10K2.u210 = KTree.node A10K2.u208 (nat_lit 2065236) (nat_lit 5147766367) (nat_lit 0) A10K2.u209 from rfl, totK_node, atot208, atot209]
  decide +kernel

theorem arows214 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u214 = true := by
  rw [show A10K2.u214 = KTree.node A10K2.u212 (nat_lit 2080190) (nat_lit 16430386221) (nat_lit 0) A10K2.u213 from rfl, allE_node, arows212, irow214, arows213]
  all_goals rfl

theorem atot214 : totK PA10K2 A10K2.u214 = [0, 0, 1426773418777, 6145431339224, 8214441328195, 3597776922476, 373498198353, 6439430839, 0, 0] := by
  rw [show A10K2.u214 = KTree.node A10K2.u212 (nat_lit 2080190) (nat_lit 16430386221) (nat_lit 0) A10K2.u213 from rfl, totK_node, atot212, atot213]
  decide +kernel

theorem arows217 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u217 = true := by
  rw [show A10K2.u217 = KTree.node A10K2.u215 (nat_lit 2097927) (nat_lit 9765509339) (nat_lit 0) A10K2.u216 from rfl, allE_node, arows215, irow217, arows216]
  all_goals rfl

theorem atot217 : totK PA10K2 A10K2.u217 = [0, 873069160064, 3614736415455, 5576617951592, 5083938499116, 3413329784504, 924548346165, 61018386929, 0, 0] := by
  rw [show A10K2.u217 = KTree.node A10K2.u215 (nat_lit 2097927) (nat_lit 9765509339) (nat_lit 0) A10K2.u216 from rfl, totK_node, atot215, atot216]
  decide +kernel

theorem arows223 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u223 = true := by
  rw [show A10K2.u223 = KTree.node A10K2.u221 (nat_lit 2116131) (nat_lit 8102234542) (nat_lit 0) A10K2.u222 from rfl, allE_node, arows221, irow223, arows222]
  all_goals rfl

theorem atot223 : totK PA10K2 A10K2.u223 = [0, 1193272473200, 5367497029126, 7889008342923, 3911903414006, 499150818378, 11814975521, 0, 0, 0] := by
  rw [show A10K2.u223 = KTree.node A10K2.u221 (nat_lit 2116131) (nat_lit 8102234542) (nat_lit 0) A10K2.u222 from rfl, totK_node, atot221, atot222]
  decide +kernel

theorem arows226 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u226 = true := by
  rw [show A10K2.u226 = KTree.node A10K2.u224 (nat_lit 2129403) (nat_lit 6187737511) (nat_lit 0) A10K2.u225 from rfl, allE_node, arows224, irow226, arows225]
  all_goals rfl

theorem atot226 : totK PA10K2 A10K2.u226 = [0, 309893393367, 2935725047612, 7713054844816, 7026226597984, 1758856524602, 85416163696, 0, 0, 0] := by
  rw [show A10K2.u226 = KTree.node A10K2.u224 (nat_lit 2129403) (nat_lit 6187737511) (nat_lit 0) A10K2.u225 from rfl, totK_node, atot224, atot225]
  decide +kernel

theorem arows230 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u230 = true := by
  rw [show A10K2.u230 = KTree.node A10K2.u228 (nat_lit 2147482) (nat_lit 9242491161) (nat_lit 0) A10K2.u229 from rfl, allE_node, arows228, irow230, arows229]
  all_goals rfl

theorem atot230 : totK PA10K2 A10K2.u230 = [0, 0, 941553305314, 4686225985371, 7701998397604, 4287517734088, 773321205799, 36196801203, 0, 0] := by
  rw [show A10K2.u230 = KTree.node A10K2.u228 (nat_lit 2147482) (nat_lit 9242491161) (nat_lit 0) A10K2.u229 from rfl, totK_node, atot228, atot229]
  decide +kernel

theorem arows233 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u233 = true := by
  rw [show A10K2.u233 = KTree.node A10K2.u231 (nat_lit 2230348) (nat_lit 10942262896) (nat_lit 0) A10K2.u232 from rfl, allE_node, arows231, irow233, arows232]
  all_goals rfl

theorem atot233 : totK PA10K2 A10K2.u233 = [0, 800376258443, 4057010375285, 7599631994462, 5758009191821, 1422737308710, 87203365710, 0, 0, 0] := by
  rw [show A10K2.u233 = KTree.node A10K2.u231 (nat_lit 2230348) (nat_lit 10942262896) (nat_lit 0) A10K2.u232 from rfl, totK_node, atot231, atot232]
  decide +kernel

theorem arows238 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u238 = true := by
  rw [show A10K2.u238 = KTree.node A10K2.u236 (nat_lit 2244964) (nat_lit 13775768551) (nat_lit 0) A10K2.u237 from rfl, allE_node, arows236, irow238, arows237]
  all_goals rfl

theorem atot238 : totK PA10K2 A10K2.u238 = [0, 1198319728372, 5556527692921, 7860970971824, 3472542860136, 423217156061, 11494708454, 0, 0, 0] := by
  rw [show A10K2.u238 = KTree.node A10K2.u236 (nat_lit 2244964) (nat_lit 13775768551) (nat_lit 0) A10K2.u237 from rfl, totK_node, atot236, atot237]
  decide +kernel

theorem arows241 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u241 = true := by
  rw [show A10K2.u241 = KTree.node A10K2.u239 (nat_lit 2265010) (nat_lit 12424752292) (nat_lit 0) A10K2.u240 from rfl, allE_node, arows239, irow241, arows240]
  all_goals rfl

theorem atot241 : totK PA10K2 A10K2.u241 = [0, 0, 2074376464328, 7412045790224, 7375804198412, 1789299253445, 87656715200, 0, 0, 0] := by
  rw [show A10K2.u241 = KTree.node A10K2.u239 (nat_lit 2265010) (nat_lit 12424752292) (nat_lit 0) A10K2.u240 from rfl, totK_node, atot239, atot240]
  decide +kernel

theorem arows245 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u245 = true := by
  rw [show A10K2.u245 = KTree.node A10K2.u243 (nat_lit 2295853) (nat_lit 6500360340) (nat_lit 0) A10K2.u244 from rfl, allE_node, arows243, irow245, arows244]
  all_goals rfl

theorem atot245 : totK PA10K2 A10K2.u245 = [0, 813651318326, 3662049949740, 6619117474149, 5790103069756, 1987400030829, 224345500730, 5976421810, 0, 0] := by
  rw [show A10K2.u245 = KTree.node A10K2.u243 (nat_lit 2295853) (nat_lit 6500360340) (nat_lit 0) A10K2.u244 from rfl, totK_node, atot243, atot244]
  decide +kernel

theorem arows248 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u248 = true := by
  rw [show A10K2.u248 = KTree.node A10K2.u246 (nat_lit 2318395) (nat_lit 5455790481) (nat_lit 0) A10K2.u247 from rfl, allE_node, arows246, irow248, arows247]
  all_goals rfl

theorem atot248 : totK PA10K2 A10K2.u248 = [0, 1313763117324, 5837472700510, 8466255122866, 4127926783873, 504989968829, 7380853412, 0, 0, 0] := by
  rw [show A10K2.u248 = KTree.node A10K2.u246 (nat_lit 2318395) (nat_lit 5455790481) (nat_lit 0) A10K2.u247 from rfl, totK_node, atot246, atot247]
  decide +kernel

theorem arows257 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u257 = true := by
  rw [show A10K2.u257 = KTree.node A10K2.u255 (nat_lit 2328648) (nat_lit 13768469267) (nat_lit 0) A10K2.u256 from rfl, allE_node, arows255, irow257, arows256]
  all_goals rfl

theorem atot257 : totK PA10K2 A10K2.u257 = [0, 0, 1359684327206, 6020781676969, 8322595481184, 3574643144648, 386367199208, 6904928264, 0, 0] := by
  rw [show A10K2.u257 = KTree.node A10K2.u255 (nat_lit 2328648) (nat_lit 13768469267) (nat_lit 0) A10K2.u256 from rfl, totK_node, atot255, atot256]
  decide +kernel

theorem arows260 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u260 = true := by
  rw [show A10K2.u260 = KTree.node A10K2.u258 (nat_lit 2353087) (nat_lit 14171926471) (nat_lit 0) A10K2.u259 from rfl, allE_node, arows258, irow260, arows259]
  all_goals rfl

theorem atot260 : totK PA10K2 A10K2.u260 = [0, 0, 1311927366856, 5643851990794, 7992958947056, 4279555061706, 737072980884, 23493225069, 0, 0] := by
  rw [show A10K2.u260 = KTree.node A10K2.u258 (nat_lit 2353087) (nat_lit 14171926471) (nat_lit 0) A10K2.u259 from rfl, totK_node, atot258, atot259]
  decide +kernel

theorem arows264 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u264 = true := by
  rw [show A10K2.u264 = KTree.node A10K2.u262 (nat_lit 2363788) (nat_lit 8814785933) (nat_lit 0) A10K2.u263 from rfl, allE_node, arows262, irow264, arows263]
  all_goals rfl

theorem atot264 : totK PA10K2 A10K2.u264 = [0, 0, 1304699017094, 5598831855370, 7728913692587, 3793498080079, 633117120231, 41908997193, 0, 0] := by
  rw [show A10K2.u264 = KTree.node A10K2.u262 (nat_lit 2363788) (nat_lit 8814785933) (nat_lit 0) A10K2.u263 from rfl, totK_node, atot262, atot263]
  decide +kernel

theorem arows267 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u267 = true := by
  rw [show A10K2.u267 = KTree.node A10K2.u265 (nat_lit 2384457) (nat_lit 9560104829) (nat_lit 0) A10K2.u266 from rfl, allE_node, arows265, irow267, arows266]
  all_goals rfl

theorem atot267 : totK PA10K2 A10K2.u267 = [0, 0, 1054429379149, 5237426491289, 8285799215341, 4060603543299, 534750849198, 12558367923, 0, 0] := by
  rw [show A10K2.u267 = KTree.node A10K2.u265 (nat_lit 2384457) (nat_lit 9560104829) (nat_lit 0) A10K2.u266 from rfl, totK_node, atot265, atot266]
  decide +kernel

theorem arows272 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u272 = true := by
  rw [show A10K2.u272 = KTree.node A10K2.u270 (nat_lit 2396161) (nat_lit 10630474206) (nat_lit 0) A10K2.u271 from rfl, allE_node, arows270, irow272, arows271]
  all_goals rfl

theorem atot272 : totK PA10K2 A10K2.u272 = [0, 0, 0, 1222158624353, 5486359775960, 7679223835678, 3695874688544, 628783974633, 30605747850, 0] := by
  rw [show A10K2.u272 = KTree.node A10K2.u270 (nat_lit 2396161) (nat_lit 10630474206) (nat_lit 0) A10K2.u271 from rfl, totK_node, atot270, atot271]
  decide +kernel

theorem arows275 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u275 = true := by
  rw [show A10K2.u275 = KTree.node A10K2.u273 (nat_lit 2417138) (nat_lit 12713845078) (nat_lit 0) A10K2.u274 from rfl, allE_node, arows273, irow275, arows274]
  all_goals rfl

theorem atot275 : totK PA10K2 A10K2.u275 = [0, 0, 579843672931, 3179882488005, 6543050308751, 5991757350541, 2108548334162, 238394709880, 5528811039, 0] := by
  rw [show A10K2.u275 = KTree.node A10K2.u273 (nat_lit 2417138) (nat_lit 12713845078) (nat_lit 0) A10K2.u274 from rfl, totK_node, atot273, atot274]
  decide +kernel

theorem arows279 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u279 = true := by
  rw [show A10K2.u279 = KTree.node A10K2.u277 (nat_lit 2499926) (nat_lit 5346847120) (nat_lit 0) A10K2.u278 from rfl, allE_node, arows277, irow279, arows278]
  all_goals rfl

theorem atot279 : totK PA10K2 A10K2.u279 = [0, 0, 1068287224037, 4871600478282, 7741617832414, 4301032282506, 728126817842, 36487828629, 0, 0] := by
  rw [show A10K2.u279 = KTree.node A10K2.u277 (nat_lit 2499926) (nat_lit 5346847120) (nat_lit 0) A10K2.u278 from rfl, totK_node, atot277, atot278]
  decide +kernel

theorem arows282 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u282 = true := by
  rw [show A10K2.u282 = KTree.node A10K2.u280 (nat_lit 2523195) (nat_lit 3162512985) (nat_lit 0) A10K2.u281 from rfl, allE_node, arows280, irow282, arows281]
  all_goals rfl

theorem atot282 : totK PA10K2 A10K2.u282 = [0, 0, 342944423181, 3451747063719, 8013814340285, 5529709568492, 1016582449568, 44905858284, 0, 0] := by
  rw [show A10K2.u282 = KTree.node A10K2.u280 (nat_lit 2523195) (nat_lit 3162512985) (nat_lit 0) A10K2.u281 from rfl, totK_node, atot280, atot281]
  decide +kernel

theorem arows288 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u288 = true := by
  rw [show A10K2.u288 = KTree.node A10K2.u286 (nat_lit 2545000) (nat_lit 8527505760) (nat_lit 0) A10K2.u287 from rfl, allE_node, arows286, irow288, arows287]
  all_goals rfl

theorem atot288 : totK PA10K2 A10K2.u288 = [0, 0, 808333325195, 3596215296470, 6420783371515, 5581870257741, 1884256402695, 228289228634, 5676195732, 0] := by
  rw [show A10K2.u288 = KTree.node A10K2.u286 (nat_lit 2545000) (nat_lit 8527505760) (nat_lit 0) A10K2.u287 from rfl, totK_node, atot286, atot287]
  decide +kernel

theorem arows291 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u291 = true := by
  rw [show A10K2.u291 = KTree.node A10K2.u289 (nat_lit 2568135) (nat_lit 14283702521) (nat_lit 0) A10K2.u290 from rfl, allE_node, arows289, irow291, arows290]
  all_goals rfl

theorem atot291 : totK PA10K2 A10K2.u291 = [0, 0, 1310498630685, 5818489185883, 8371276492178, 3970230601226, 503238198380, 20058242317, 0, 0] := by
  rw [show A10K2.u291 = KTree.node A10K2.u289 (nat_lit 2568135) (nat_lit 14283702521) (nat_lit 0) A10K2.u290 from rfl, totK_node, atot289, atot290]
  decide +kernel

theorem arows295 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u295 = true := by
  rw [show A10K2.u295 = KTree.node A10K2.u293 (nat_lit 3148442) (nat_lit 11258513416) (nat_lit 0) A10K2.u294 from rfl, allE_node, arows293, irow295, arows294]
  all_goals rfl

theorem atot295 : totK PA10K2 A10K2.u295 = [0, 840936427454, 3862057551981, 6440756198440, 5174341563440, 2570930862376, 592294178242, 35503361870, 0, 0] := by
  rw [show A10K2.u295 = KTree.node A10K2.u293 (nat_lit 3148442) (nat_lit 11258513416) (nat_lit 0) A10K2.u294 from rfl, totK_node, atot293, atot294]
  decide +kernel

theorem arows298 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u298 = true := by
  rw [show A10K2.u298 = KTree.node A10K2.u296 (nat_lit 3167404) (nat_lit 12833588919) (nat_lit 0) A10K2.u297 from rfl, allE_node, arows296, irow298, arows297]
  all_goals rfl

theorem atot298 : totK PA10K2 A10K2.u298 = [0, 1349314439638, 5835163563979, 8040530720242, 3613889874519, 437650337450, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u298 = KTree.node A10K2.u296 (nat_lit 3167404) (nat_lit 12833588919) (nat_lit 0) A10K2.u297 from rfl, totK_node, atot296, atot297]
  decide +kernel

theorem arows303 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u303 = true := by
  rw [show A10K2.u303 = KTree.node A10K2.u301 (nat_lit 3181210) (nat_lit 10568189681) (nat_lit 0) A10K2.u302 from rfl, allE_node, arows301, irow303, arows302]
  all_goals rfl

theorem atot303 : totK PA10K2 A10K2.u303 = [0, 0, 1311751725632, 5745940087570, 7951958878668, 3660071278582, 600325762398, 30650496230, 0, 0] := by
  rw [show A10K2.u303 = KTree.node A10K2.u301 (nat_lit 3181210) (nat_lit 10568189681) (nat_lit 0) A10K2.u302 from rfl, totK_node, atot301, atot302]
  decide +kernel

theorem arows306 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u306 = true := by
  rw [show A10K2.u306 = KTree.node A10K2.u304 (nat_lit 3201060) (nat_lit 13755931144) (nat_lit 0) A10K2.u305 from rfl, allE_node, arows304, irow306, arows305]
  all_goals rfl

theorem atot306 : totK PA10K2 A10K2.u306 = [0, 293929698888, 2242709052198, 6307972655838, 7321784352897, 2801299514346, 296781960432, 5546304973, 0, 0] := by
  rw [show A10K2.u306 = KTree.node A10K2.u304 (nat_lit 3201060) (nat_lit 13755931144) (nat_lit 0) A10K2.u305 from rfl, totK_node, atot304, atot305]
  decide +kernel

theorem arows310 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u310 = true := by
  rw [show A10K2.u310 = KTree.node A10K2.u308 (nat_lit 3227989) (nat_lit 6943473206) (nat_lit 0) A10K2.u309 from rfl, allE_node, arows308, irow310, arows309]
  all_goals rfl

theorem atot310 : totK PA10K2 A10K2.u310 = [0, 1007400763894, 5022560187075, 7959753402433, 4284021996831, 706153237557, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u310 = KTree.node A10K2.u308 (nat_lit 3227989) (nat_lit 6943473206) (nat_lit 0) A10K2.u309 from rfl, totK_node, atot308, atot309]
  decide +kernel

theorem arows313 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u313 = true := by
  rw [show A10K2.u313 = KTree.node A10K2.u311 (nat_lit 3261778) (nat_lit 14924499148) (nat_lit 0) A10K2.u312 from rfl, allE_node, arows311, irow313, arows312]
  all_goals rfl

theorem atot313 : totK PA10K2 A10K2.u313 = [0, 174706470648, 1796103277991, 6223936423889, 7545922934928, 2733009438328, 282319271820, 6121173289, 0, 0] := by
  rw [show A10K2.u313 = KTree.node A10K2.u311 (nat_lit 3261778) (nat_lit 14924499148) (nat_lit 0) A10K2.u312 from rfl, totK_node, atot311, atot312]
  decide +kernel

theorem arows320 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u320 = true := by
  rw [show A10K2.u320 = KTree.node A10K2.u318 (nat_lit 3282957) (nat_lit 5811818217) (nat_lit 0) A10K2.u319 from rfl, allE_node, arows318, irow320, arows319]
  all_goals rfl

theorem atot320 : totK PA10K2 A10K2.u320 = [0, 1174675289230, 5375238936935, 7869449166606, 4011841034713, 658417856034, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u320 = KTree.node A10K2.u318 (nat_lit 3282957) (nat_lit 5811818217) (nat_lit 0) A10K2.u319 from rfl, totK_node, atot318, atot319]
  decide +kernel

theorem arows323 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u323 = true := by
  rw [show A10K2.u323 = KTree.node A10K2.u321 (nat_lit 3295008) (nat_lit 10850459610) (nat_lit 0) A10K2.u322 from rfl, allE_node, arows321, irow323, arows322]
  all_goals rfl

theorem atot323 : totK PA10K2 A10K2.u323 = [0, 821360382996, 4487729160566, 7794307609196, 4646516029238, 810911272343, 37688169288, 0, 0, 0] := by
  rw [show A10K2.u323 = KTree.node A10K2.u321 (nat_lit 3295008) (nat_lit 10850459610) (nat_lit 0) A10K2.u322 from rfl, totK_node, atot321, atot322]
  decide +kernel

theorem arows327 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u327 = true := by
  rw [show A10K2.u327 = KTree.node A10K2.u325 (nat_lit 3320044) (nat_lit 11971357676) (nat_lit 0) A10K2.u326 from rfl, allE_node, arows325, irow327, arows326]
  all_goals rfl

theorem atot327 : totK PA10K2 A10K2.u327 = [0, 0, 1949546688601, 7237627366861, 7568155399398, 1964205788301, 121086437264, 0, 0, 0] := by
  rw [show A10K2.u327 = KTree.node A10K2.u325 (nat_lit 3320044) (nat_lit 11971357676) (nat_lit 0) A10K2.u326 from rfl, totK_node, atot325, atot326]
  decide +kernel

theorem arows330 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u330 = true := by
  rw [show A10K2.u330 = KTree.node A10K2.u328 (nat_lit 3410180) (nat_lit 13192877467) (nat_lit 0) A10K2.u329 from rfl, allE_node, arows328, irow330, arows329]
  all_goals rfl

theorem atot330 : totK PA10K2 A10K2.u330 = [0, 0, 839786882131, 4590569238566, 7996077273508, 4511572334116, 822121392647, 37172849495, 0, 0] := by
  rw [show A10K2.u330 = KTree.node A10K2.u328 (nat_lit 3410180) (nat_lit 13192877467) (nat_lit 0) A10K2.u329 from rfl, totK_node, atot328, atot329]
  decide +kernel

theorem arows335 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u335 = true := by
  rw [show A10K2.u335 = KTree.node A10K2.u333 (nat_lit 3428744) (nat_lit 14279013696) (nat_lit 0) A10K2.u334 from rfl, allE_node, arows333, irow335, arows334]
  all_goals rfl

theorem atot335 : totK PA10K2 A10K2.u335 = [0, 0, 1345944286287, 5912969064228, 8150531221397, 3394189719368, 351883656491, 6354482628, 0, 0] := by
  rw [show A10K2.u335 = KTree.node A10K2.u333 (nat_lit 3428744) (nat_lit 14279013696) (nat_lit 0) A10K2.u334 from rfl, totK_node, atot333, atot334]
  decide +kernel

theorem arows338 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u338 = true := by
  rw [show A10K2.u338 = KTree.node A10K2.u336 (nat_lit 3490093) (nat_lit 6613758113) (nat_lit 0) A10K2.u337 from rfl, allE_node, arows336, irow338, arows337]
  all_goals rfl

theorem atot338 : totK PA10K2 A10K2.u338 = [0, 0, 1298700817108, 5875576237892, 8069565751477, 3435483956896, 395936097986, 6853348008, 0, 0] := by
  rw [show A10K2.u338 = KTree.node A10K2.u336 (nat_lit 3490093) (nat_lit 6613758113) (nat_lit 0) A10K2.u337 from rfl, totK_node, atot336, atot337]
  decide +kernel

theorem arows342 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u342 = true := by
  rw [show A10K2.u342 = KTree.node A10K2.u340 (nat_lit 3543336) (nat_lit 12390657786) (nat_lit 0) A10K2.u341 from rfl, allE_node, arows340, irow342, arows341]
  all_goals rfl

theorem atot342 : totK PA10K2 A10K2.u342 = [0, 0, 1281383918015, 5361618206200, 7577753067921, 3903835249315, 670908486315, 36429366174, 0, 0] := by
  rw [show A10K2.u342 = KTree.node A10K2.u340 (nat_lit 3543336) (nat_lit 12390657786) (nat_lit 0) A10K2.u341 from rfl, totK_node, atot340, atot341]
  decide +kernel

theorem arows345 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u345 = true := by
  rw [show A10K2.u345 = KTree.node A10K2.u343 (nat_lit 3557156) (nat_lit 13942110594) (nat_lit 0) A10K2.u344 from rfl, allE_node, arows343, irow345, arows344]
  all_goals rfl

theorem atot345 : totK PA10K2 A10K2.u345 = [0, 0, 883609125604, 4855020960255, 8113027743483, 4049255363738, 548328568517, 12388698189, 0, 0] := by
  rw [show A10K2.u345 = KTree.node A10K2.u343 (nat_lit 3557156) (nat_lit 13942110594) (nat_lit 0) A10K2.u344 from rfl, totK_node, atot343, atot344]
  decide +kernel

theorem arows351 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u351 = true := by
  rw [show A10K2.u351 = KTree.node A10K2.u349 (nat_lit 3588194) (nat_lit 7868795810) (nat_lit 0) A10K2.u350 from rfl, allE_node, arows349, irow351, arows350]
  all_goals rfl

theorem atot351 : totK PA10K2 A10K2.u351 = [0, 0, 0, 1924617490758, 7186589737323, 7139635141561, 1909079559496, 125963515320, 0, 0] := by
  rw [show A10K2.u351 = KTree.node A10K2.u349 (nat_lit 3588194) (nat_lit 7868795810) (nat_lit 0) A10K2.u350 from rfl, totK_node, atot349, atot350]
  decide +kernel

theorem arows354 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u354 = true := by
  rw [show A10K2.u354 = KTree.node A10K2.u352 (nat_lit 3674034) (nat_lit 13201832723) (nat_lit 0) A10K2.u353 from rfl, allE_node, arows352, irow354, arows353]
  all_goals rfl

theorem atot354 : totK PA10K2 A10K2.u354 = [0, 1132878220426, 4890926435051, 7088533597551, 3900068823396, 1308717718557, 669069647881, 135399462593, 5976421810, 0] := by
  rw [show A10K2.u354 = KTree.node A10K2.u352 (nat_lit 3674034) (nat_lit 13201832723) (nat_lit 0) A10K2.u353 from rfl, totK_node, atot352, atot353]
  decide +kernel

theorem arows358 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u358 = true := by
  rw [show A10K2.u358 = KTree.node A10K2.u356 (nat_lit 3695826) (nat_lit 15611215237) (nat_lit 0) A10K2.u357 from rfl, allE_node, arows356, irow358, arows357]
  all_goals rfl

theorem atot358 : totK PA10K2 A10K2.u358 = [0, 1076691216300, 5175589297423, 8159030754328, 4557776743096, 731304464728, 19519631524, 0, 0, 0] := by
  rw [show A10K2.u358 = KTree.node A10K2.u356 (nat_lit 3695826) (nat_lit 15611215237) (nat_lit 0) A10K2.u357 from rfl, totK_node, atot356, atot357]
  decide +kernel

theorem arows361 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u361 = true := by
  rw [show A10K2.u361 = KTree.node A10K2.u359 (nat_lit 3706359) (nat_lit 14964360840) (nat_lit 0) A10K2.u360 from rfl, allE_node, arows359, irow361, arows360]
  all_goals rfl

theorem atot361 : totK PA10K2 A10K2.u361 = [0, 0, 1343818136979, 5717303889098, 7810522292230, 3751080593834, 638197483266, 30650496230, 0, 0] := by
  rw [show A10K2.u361 = KTree.node A10K2.u359 (nat_lit 3706359) (nat_lit 14964360840) (nat_lit 0) A10K2.u360 from rfl, totK_node, atot359, atot360]
  decide +kernel

theorem arows366 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u366 = true := by
  rw [show A10K2.u366 = KTree.node A10K2.u364 (nat_lit 3731009) (nat_lit 10222429166) (nat_lit 0) A10K2.u365 from rfl, allE_node, arows364, irow366, arows365]
  all_goals rfl

theorem atot366 : totK PA10K2 A10K2.u366 = [0, 593289185904, 3555004706191, 7582762070969, 6449740971397, 1725278952714, 114389054536, 0, 0, 0] := by
  rw [show A10K2.u366 = KTree.node A10K2.u364 (nat_lit 3731009) (nat_lit 10222429166) (nat_lit 0) A10K2.u365 from rfl, totK_node, atot364, atot365]
  decide +kernel

theorem arows369 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u369 = true := by
  rw [show A10K2.u369 = KTree.node A10K2.u367 (nat_lit 3764229) (nat_lit 5541860323) (nat_lit 0) A10K2.u368 from rfl, allE_node, arows367, irow369, arows368]
  all_goals rfl

theorem atot369 : totK PA10K2 A10K2.u369 = [0, 794660274798, 4311665447779, 8051521265782, 5822367467037, 1417432775330, 88695296450, 0, 0, 0] := by
  rw [show A10K2.u369 = KTree.node A10K2.u367 (nat_lit 3764229) (nat_lit 5541860323) (nat_lit 0) A10K2.u368 from rfl, totK_node, atot367, atot368]
  decide +kernel

theorem arows373 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u373 = true := by
  rw [show A10K2.u373 = KTree.node A10K2.u371 (nat_lit 3794134) (nat_lit 15000960781) (nat_lit 0) A10K2.u372 from rfl, allE_node, arows371, irow373, arows372]
  all_goals rfl

theorem atot373 : totK PA10K2 A10K2.u373 = [0, 473630045979, 2778207823671, 6385218228228, 7007390793802, 3047259680945, 363950582087, 7380853412, 0, 0] := by
  rw [show A10K2.u373 = KTree.node A10K2.u371 (nat_lit 3794134) (nat_lit 15000960781) (nat_lit 0) A10K2.u372 from rfl, totK_node, atot371, atot372]
  decide +kernel

theorem arows376 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u376 = true := by
  rw [show A10K2.u376 = KTree.node A10K2.u374 (nat_lit 3876024) (nat_lit 9579324132) (nat_lit 0) A10K2.u375 from rfl, allE_node, arows374, irow376, arows375]
  all_goals rfl

theorem atot376 : totK PA10K2 A10K2.u376 = [0, 935537785808, 4771615087309, 8253592522308, 5089752262074, 910130200671, 37987813032, 0, 0, 0] := by
  rw [show A10K2.u376 = KTree.node A10K2.u374 (nat_lit 3876024) (nat_lit 9579324132) (nat_lit 0) A10K2.u375 from rfl, totK_node, atot374, atot375]
  decide +kernel

theorem arows384 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u384 = true := by
  rw [show A10K2.u384 = KTree.node A10K2.u382 (nat_lit 3895330) (nat_lit 2268323983) (nat_lit 0) A10K2.u383 from rfl, allE_node, arows382, irow384, arows383]
  all_goals rfl

theorem atot384 : totK PA10K2 A10K2.u384 = [0, 873621053165, 4500752903426, 7923387368691, 5359175156401, 1157020896148, 62996513375, 0, 0, 0] := by
  rw [show A10K2.u384 = KTree.node A10K2.u382 (nat_lit 3895330) (nat_lit 2268323983) (nat_lit 0) A10K2.u383 from rfl, totK_node, atot382, atot383]
  decide +kernel

theorem arows387 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u387 = true := by
  rw [show A10K2.u387 = KTree.node A10K2.u385 (nat_lit 3906593) (nat_lit 10029294968) (nat_lit 0) A10K2.u386 from rfl, allE_node, arows385, irow387, arows386]
  all_goals rfl

theorem atot387 : totK PA10K2 A10K2.u387 = [0, 0, 1106117150827, 5409971977294, 8397899606593, 4310773281395, 572335024867, 13671283666, 0, 0] := by
  rw [show A10K2.u387 = KTree.node A10K2.u385 (nat_lit 3906593) (nat_lit 10029294968) (nat_lit 0) A10K2.u386 from rfl, totK_node, atot385, atot386]
  decide +kernel

theorem arows391 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u391 = true := by
  rw [show A10K2.u391 = KTree.node A10K2.u389 (nat_lit 3927728) (nat_lit 11491732919) (nat_lit 0) A10K2.u390 from rfl, allE_node, arows389, irow391, arows390]
  all_goals rfl

theorem atot391 : totK PA10K2 A10K2.u391 = [132922702514, 322593360771, 1059345455841, 4449550572167, 7610121793976, 5049582598897, 1073448159147, 61110126106, 0, 0] := by
  rw [show A10K2.u391 = KTree.node A10K2.u389 (nat_lit 3927728) (nat_lit 11491732919) (nat_lit 0) A10K2.u390 from rfl, totK_node, atot389, atot390]
  decide +kernel

theorem arows394 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u394 = true := by
  rw [show A10K2.u394 = KTree.node A10K2.u392 (nat_lit 8393260) (nat_lit 11339850944) (nat_lit 0) A10K2.u393 from rfl, allE_node, arows392, irow394, arows393]
  all_goals rfl

theorem atot394 : totK PA10K2 A10K2.u394 = [1196291941578, 5331958587436, 7880050535489, 4136904325038, 676501523260, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u394 = KTree.node A10K2.u392 (nat_lit 8393260) (nat_lit 11339850944) (nat_lit 0) A10K2.u393 from rfl, totK_node, atot392, atot393]
  decide +kernel

theorem arows399 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u399 = true := by
  rw [show A10K2.u399 = KTree.node A10K2.u397 (nat_lit 8413769) (nat_lit 9560104829) (nat_lit 0) A10K2.u398 from rfl, allE_node, arows397, irow399, arows398]
  all_goals rfl

theorem atot399 : totK PA10K2 A10K2.u399 = [950866415105, 5000911661576, 8340228059769, 4788704080090, 727880422571, 13207830636, 0, 0, 0, 0] := by
  rw [show A10K2.u399 = KTree.node A10K2.u397 (nat_lit 8413769) (nat_lit 9560104829) (nat_lit 0) A10K2.u398 from rfl, totK_node, atot397, atot398]
  decide +kernel

theorem arows402 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u402 = true := by
  rw [show A10K2.u402 = KTree.node A10K2.u400 (nat_lit 8425472) (nat_lit 15792662511) (nat_lit 0) A10K2.u401 from rfl, allE_node, arows400, irow402, arows401]
  all_goals rfl

theorem atot402 : totK PA10K2 A10K2.u402 = [0, 1213995086113, 5432874340824, 7925932558631, 3951224580610, 655059766175, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u402 = KTree.node A10K2.u400 (nat_lit 8425472) (nat_lit 15792662511) (nat_lit 0) A10K2.u401 from rfl, totK_node, atot400, atot401]
  decide +kernel

theorem arows406 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u406 = true := by
  rw [show A10K2.u406 = KTree.node A10K2.u404 (nat_lit 8446344) (nat_lit 14229919885) (nat_lit 0) A10K2.u405 from rfl, allE_node, arows404, irow406, arows405]
  all_goals rfl

theorem atot406 : totK PA10K2 A10K2.u406 = [568825667955, 2767205613469, 6283258436149, 6817246741643, 2623739938300, 274756864293, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u406 = KTree.node A10K2.u404 (nat_lit 8446344) (nat_lit 14229919885) (nat_lit 0) A10K2.u405 from rfl, totK_node, atot404, atot405]
  decide +kernel

theorem arows409 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u409 = true := by
  rw [show A10K2.u409 = KTree.node A10K2.u407 (nat_lit 8527326) (nat_lit 14060443749) (nat_lit 0) A10K2.u408 from rfl, allE_node, arows407, irow409, arows408]
  all_goals rfl

theorem atot409 : totK PA10K2 A10K2.u409 = [722043574644, 4358462663912, 7920047166763, 5050063640203, 1003460739135, 56566207178, 0, 0, 0, 0] := by
  rw [show A10K2.u409 = KTree.node A10K2.u407 (nat_lit 8527326) (nat_lit 14060443749) (nat_lit 0) A10K2.u408 from rfl, totK_node, atot407, atot408]
  decide +kernel

end QECKChecks.A10K2
