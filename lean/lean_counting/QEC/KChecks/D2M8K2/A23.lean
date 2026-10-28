import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A22

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows12096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12096 = true := by
  rw [show D2M8K2.u12096 = KTree.node D2M8K2.u12092 (nat_lit 25770248) (nat_lit 3606527351) (nat_lit 0) D2M8K2.u12095 from rfl, allE_node, arows12092, irow12096, arows12095]
  all_goals rfl

theorem atot12096 : totK PD2M8K2 D2M8K2.u12096 = [0, 822030395565, 2945796775715, 2799429980415, 567217204105, 18301866131, 0, 0] := by
  rw [show D2M8K2.u12096 = KTree.node D2M8K2.u12092 (nat_lit 25770248) (nat_lit 3606527351) (nat_lit 0) D2M8K2.u12095 from rfl, totK_node, atot12092, atot12095]
  decide +kernel

theorem arows12103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12103 = true := by
  rw [show D2M8K2.u12103 = KTree.node D2M8K2.u12099 (nat_lit 25777539) (nat_lit 3002051844) (nat_lit 0) D2M8K2.u12102 from rfl, allE_node, arows12099, irow12103, arows12102]
  all_goals rfl

theorem atot12103 : totK PD2M8K2 D2M8K2.u12103 = [0, 0, 1272450908690, 3568109610724, 2022715818677, 190041352942, 1217496766, 0] := by
  rw [show D2M8K2.u12103 = KTree.node D2M8K2.u12099 (nat_lit 25777539) (nat_lit 3002051844) (nat_lit 0) D2M8K2.u12102 from rfl, totK_node, atot12099, atot12102]
  decide +kernel

theorem arows12111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12111 = true := by
  rw [show D2M8K2.u12111 = KTree.node D2M8K2.u12107 (nat_lit 25789497) (nat_lit 1879352740) (nat_lit 0) D2M8K2.u12110 from rfl, allE_node, arows12107, irow12111, arows12110]
  all_goals rfl

theorem atot12111 : totK PD2M8K2 D2M8K2.u12111 = [0, 0, 915639657489, 3068444246475, 2483502895763, 478695873240, 17736366219, 0] := by
  rw [show D2M8K2.u12111 = KTree.node D2M8K2.u12107 (nat_lit 25789497) (nat_lit 1879352740) (nat_lit 0) D2M8K2.u12110 from rfl, totK_node, atot12107, atot12110]
  decide +kernel

theorem arows12118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12118 = true := by
  rw [show D2M8K2.u12118 = KTree.node D2M8K2.u12114 (nat_lit 25798882) (nat_lit 4155525070) (nat_lit 0) D2M8K2.u12117 from rfl, allE_node, arows12114, irow12118, arows12117]
  all_goals rfl

theorem atot12118 : totK PD2M8K2 D2M8K2.u12118 = [0, 824634681466, 2929870833748, 2793213994373, 647605199636, 25419901180, 0, 0] := by
  rw [show D2M8K2.u12118 = KTree.node D2M8K2.u12114 (nat_lit 25798882) (nat_lit 4155525070) (nat_lit 0) D2M8K2.u12117 from rfl, totK_node, atot12114, atot12117]
  decide +kernel

theorem arows12127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12127 = true := by
  rw [show D2M8K2.u12127 = KTree.node D2M8K2.u12123 (nat_lit 25806352) (nat_lit 3155787989) (nat_lit 0) D2M8K2.u12126 from rfl, allE_node, arows12123, irow12127, arows12126]
  all_goals rfl

theorem atot12127 : totK PD2M8K2 D2M8K2.u12127 = [0, 861238645375, 2999745957287, 2754061282046, 551773685211, 17783489906, 0, 0] := by
  rw [show D2M8K2.u12127 = KTree.node D2M8K2.u12123 (nat_lit 25806352) (nat_lit 3155787989) (nat_lit 0) D2M8K2.u12126 from rfl, totK_node, atot12123, atot12126]
  decide +kernel

theorem arows12134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12134 = true := by
  rw [show D2M8K2.u12134 = KTree.node D2M8K2.u12130 (nat_lit 25816587) (nat_lit 580222479) (nat_lit 0) D2M8K2.u12133 from rfl, allE_node, arows12130, irow12134, arows12133]
  all_goals rfl

theorem atot12134 : totK PD2M8K2 D2M8K2.u12134 = [0, 345349101557, 1991010832810, 3264999260350, 1380857920346, 107273987272, 1138244013, 0] := by
  rw [show D2M8K2.u12134 = KTree.node D2M8K2.u12130 (nat_lit 25816587) (nat_lit 580222479) (nat_lit 0) D2M8K2.u12133 from rfl, totK_node, atot12130, atot12133]
  decide +kernel

theorem arows12142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12142 = true := by
  rw [show D2M8K2.u12142 = KTree.node D2M8K2.u12138 (nat_lit 25828136) (nat_lit 2510560713) (nat_lit 0) D2M8K2.u12141 from rfl, allE_node, arows12138, irow12142, arows12141]
  all_goals rfl

theorem atot12142 : totK PD2M8K2 D2M8K2.u12142 = [0, 0, 1339279834661, 3573408528021, 1902919971155, 179525335473, 2162517376, 0] := by
  rw [show D2M8K2.u12142 = KTree.node D2M8K2.u12138 (nat_lit 25828136) (nat_lit 2510560713) (nat_lit 0) D2M8K2.u12141 from rfl, totK_node, atot12138, atot12141]
  decide +kernel

theorem arows12149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12149 = true := by
  rw [show D2M8K2.u12149 = KTree.node D2M8K2.u12145 (nat_lit 25840995) (nat_lit 3693876886) (nat_lit 0) D2M8K2.u12148 from rfl, allE_node, arows12145, irow12149, arows12148]
  all_goals rfl

theorem atot12149 : totK PD2M8K2 D2M8K2.u12149 = [0, 803610989290, 2856476572594, 2760755636211, 721423661102, 67363384151, 2751766863, 0] := by
  rw [show D2M8K2.u12149 = KTree.node D2M8K2.u12145 (nat_lit 25840995) (nat_lit 3693876886) (nat_lit 0) D2M8K2.u12148 from rfl, totK_node, atot12145, atot12148]
  decide +kernel

theorem arows12160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12160 = true := by
  rw [show D2M8K2.u12160 = KTree.node D2M8K2.u12156 (nat_lit 25850552) (nat_lit 3853028152) (nat_lit 0) D2M8K2.u12159 from rfl, allE_node, arows12156, irow12160, arows12159]
  all_goals rfl

theorem atot12160 : totK PD2M8K2 D2M8K2.u12160 = [0, 852251308592, 2940598785499, 2758098976963, 637558589783, 23703997050, 0, 0] := by
  rw [show D2M8K2.u12160 = KTree.node D2M8K2.u12156 (nat_lit 25850552) (nat_lit 3853028152) (nat_lit 0) D2M8K2.u12159 from rfl, totK_node, atot12156, atot12159]
  decide +kernel

theorem arows12167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12167 = true := by
  rw [show D2M8K2.u12167 = KTree.node D2M8K2.u12163 (nat_lit 25881243) (nat_lit 3005410253) (nat_lit 0) D2M8K2.u12166 from rfl, allE_node, arows12163, irow12167, arows12166]
  all_goals rfl

theorem atot12167 : totK PD2M8K2 D2M8K2.u12167 = [845908722094, 2850705172695, 2514317878387, 746785677652, 213234460089, 17080783126, 0, 0] := by
  rw [show D2M8K2.u12167 = KTree.node D2M8K2.u12163 (nat_lit 25881243) (nat_lit 3005410253) (nat_lit 0) D2M8K2.u12166 from rfl, totK_node, atot12163, atot12166]
  decide +kernel

theorem arows12175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12175 = true := by
  rw [show D2M8K2.u12175 = KTree.node D2M8K2.u12171 (nat_lit 25891741) (nat_lit 981433207) (nat_lit 0) D2M8K2.u12174 from rfl, allE_node, arows12171, irow12175, arows12174]
  all_goals rfl

theorem atot12175 : totK PD2M8K2 D2M8K2.u12175 = [834957209315, 2959860475578, 2785086060031, 573237869894, 17809204495, 0, 0, 0] := by
  rw [show D2M8K2.u12175 = KTree.node D2M8K2.u12171 (nat_lit 25891741) (nat_lit 981433207) (nat_lit 0) D2M8K2.u12174 from rfl, totK_node, atot12171, atot12174]
  decide +kernel

theorem arows12182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12182 = true := by
  rw [show D2M8K2.u12182 = KTree.node D2M8K2.u12178 (nat_lit 25899140) (nat_lit 1664023632) (nat_lit 0) D2M8K2.u12181 from rfl, allE_node, arows12178, irow12182, arows12181]
  all_goals rfl

theorem atot12182 : totK PD2M8K2 D2M8K2.u12182 = [323074992700, 1760608929523, 3110737770135, 1653056068906, 190418322806, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12182 = KTree.node D2M8K2.u12178 (nat_lit 25899140) (nat_lit 1664023632) (nat_lit 0) D2M8K2.u12181 from rfl, totK_node, atot12178, atot12181]
  decide +kernel

theorem arows12191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12191 = true := by
  rw [show D2M8K2.u12191 = KTree.node D2M8K2.u12187 (nat_lit 25911118) (nat_lit 3265608921) (nat_lit 0) D2M8K2.u12190 from rfl, allE_node, arows12187, irow12191, arows12190]
  all_goals rfl

theorem atot12191 : totK PD2M8K2 D2M8K2.u12191 = [0, 1490983207559, 3796569332071, 1751674984378, 85930539523, 0, 0, 0] := by
  rw [show D2M8K2.u12191 = KTree.node D2M8K2.u12187 (nat_lit 25911118) (nat_lit 3265608921) (nat_lit 0) D2M8K2.u12190 from rfl, totK_node, atot12187, atot12190]
  decide +kernel

theorem arows12198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12198 = true := by
  rw [show D2M8K2.u12198 = KTree.node D2M8K2.u12194 (nat_lit 25926146) (nat_lit 4027104210) (nat_lit 0) D2M8K2.u12197 from rfl, allE_node, arows12194, irow12198, arows12197]
  all_goals rfl

theorem atot12198 : totK PD2M8K2 D2M8K2.u12198 = [857647101323, 2812690625278, 2733344259048, 846667533855, 52241386291, 0, 0, 0] := by
  rw [show D2M8K2.u12198 = KTree.node D2M8K2.u12194 (nat_lit 25926146) (nat_lit 4027104210) (nat_lit 0) D2M8K2.u12197 from rfl, totK_node, atot12194, atot12197]
  decide +kernel

theorem arows12206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12206 = true := by
  rw [show D2M8K2.u12206 = KTree.node D2M8K2.u12202 (nat_lit 25932449) (nat_lit 1693941756) (nat_lit 0) D2M8K2.u12205 from rfl, allE_node, arows12202, irow12206, arows12205]
  all_goals rfl

theorem atot12206 : totK PD2M8K2 D2M8K2.u12206 = [839239039437, 2916219957375, 2789174576226, 642001720127, 26206852349, 0, 0, 0] := by
  rw [show D2M8K2.u12206 = KTree.node D2M8K2.u12202 (nat_lit 25932449) (nat_lit 1693941756) (nat_lit 0) D2M8K2.u12205 from rfl, totK_node, atot12202, atot12205]
  decide +kernel

theorem arows12213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12213 = true := by
  rw [show D2M8K2.u12213 = KTree.node D2M8K2.u12209 (nat_lit 25939950) (nat_lit 4079165587) (nat_lit 0) D2M8K2.u12212 from rfl, allE_node, arows12209, irow12213, arows12212]
  all_goals rfl

theorem atot12213 : totK PD2M8K2 D2M8K2.u12213 = [330028431640, 1976945875408, 3226152648385, 1506915249683, 253174158196, 21385604922, 0, 0] := by
  rw [show D2M8K2.u12213 = KTree.node D2M8K2.u12209 (nat_lit 25939950) (nat_lit 4079165587) (nat_lit 0) D2M8K2.u12212 from rfl, totK_node, atot12209, atot12212]
  decide +kernel

theorem arows12223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12223 = true := by
  rw [show D2M8K2.u12223 = KTree.node D2M8K2.u12219 (nat_lit 25949507) (nat_lit 2341866510) (nat_lit 0) D2M8K2.u12222 from rfl, allE_node, arows12219, irow12223, arows12222]
  all_goals rfl

theorem atot12223 : totK PD2M8K2 D2M8K2.u12223 = [0, 825838999993, 2901318318365, 2797275958508, 656508824903, 20696137567, 0, 0] := by
  rw [show D2M8K2.u12223 = KTree.node D2M8K2.u12219 (nat_lit 25949507) (nat_lit 2341866510) (nat_lit 0) D2M8K2.u12222 from rfl, totK_node, atot12219, atot12222]
  decide +kernel

theorem arows12230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12230 = true := by
  rw [show D2M8K2.u12230 = KTree.node D2M8K2.u12226 (nat_lit 25956713) (nat_lit 1178752710) (nat_lit 0) D2M8K2.u12229 from rfl, allE_node, arows12226, irow12230, arows12229]
  all_goals rfl

theorem atot12230 : totK PD2M8K2 D2M8K2.u12230 = [0, 752817351083, 2909669129383, 2982365672437, 579484794706, 9118093612, 0, 0] := by
  rw [show D2M8K2.u12230 = KTree.node D2M8K2.u12226 (nat_lit 25956713) (nat_lit 1178752710) (nat_lit 0) D2M8K2.u12229 from rfl, totK_node, atot12226, atot12229]
  decide +kernel

theorem arows12238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12238 = true := by
  rw [show D2M8K2.u12238 = KTree.node D2M8K2.u12234 (nat_lit 25965250) (nat_lit 4061605012) (nat_lit 0) D2M8K2.u12237 from rfl, allE_node, arows12234, irow12238, arows12237]
  all_goals rfl

theorem atot12238 : totK PD2M8K2 D2M8K2.u12238 = [824500821324, 2852942482859, 2653514268492, 754600434550, 122896513812, 6818291842, 0, 0] := by
  rw [show D2M8K2.u12238 = KTree.node D2M8K2.u12234 (nat_lit 25965250) (nat_lit 4061605012) (nat_lit 0) D2M8K2.u12237 from rfl, totK_node, atot12234, atot12237]
  decide +kernel

theorem arows12245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12245 = true := by
  rw [show D2M8K2.u12245 = KTree.node D2M8K2.u12241 (nat_lit 25970850) (nat_lit 1324325430) (nat_lit 0) D2M8K2.u12244 from rfl, allE_node, arows12241, irow12245, arows12244]
  all_goals rfl

theorem atot12245 : totK PD2M8K2 D2M8K2.u12245 = [864568476510, 2947251003695, 2773632995636, 631597242359, 22182624040, 0, 0, 0] := by
  rw [show D2M8K2.u12245 = KTree.node D2M8K2.u12241 (nat_lit 25970850) (nat_lit 1324325430) (nat_lit 0) D2M8K2.u12244 from rfl, totK_node, atot12241, atot12244]
  decide +kernel

theorem arows12254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12254 = true := by
  rw [show D2M8K2.u12254 = KTree.node D2M8K2.u12250 (nat_lit 25982070) (nat_lit 2658989556) (nat_lit 0) D2M8K2.u12253 from rfl, allE_node, arows12250, irow12254, arows12253]
  all_goals rfl

theorem atot12254 : totK PD2M8K2 D2M8K2.u12254 = [326127760768, 1853498177060, 3205727122209, 1573176542948, 150258457995, 1206465782, 0, 0] := by
  rw [show D2M8K2.u12254 = KTree.node D2M8K2.u12250 (nat_lit 25982070) (nat_lit 2658989556) (nat_lit 0) D2M8K2.u12253 from rfl, totK_node, atot12250, atot12253]
  decide +kernel

theorem arows12261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12261 = true := by
  rw [show D2M8K2.u12261 = KTree.node D2M8K2.u12257 (nat_lit 25990632) (nat_lit 3197815384) (nat_lit 0) D2M8K2.u12260 from rfl, allE_node, arows12257, irow12261, arows12260]
  all_goals rfl

theorem atot12261 : totK PD2M8K2 D2M8K2.u12261 = [0, 1132091916580, 3332892432107, 2314400642515, 368248054858, 13016197374, 0, 0] := by
  rw [show D2M8K2.u12261 = KTree.node D2M8K2.u12257 (nat_lit 25990632) (nat_lit 3197815384) (nat_lit 0) D2M8K2.u12260 from rfl, totK_node, atot12257, atot12260]
  decide +kernel

theorem arows12269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12269 = true := by
  rw [show D2M8K2.u12269 = KTree.node D2M8K2.u12265 (nat_lit 26003168) (nat_lit 3632077801) (nat_lit 0) D2M8K2.u12268 from rfl, allE_node, arows12265, irow12269, arows12268]
  all_goals rfl

theorem atot12269 : totK PD2M8K2 D2M8K2.u12269 = [554443262464, 2139092507901, 2821563411911, 1409915561118, 191541259900, 4574395652, 0, 0] := by
  rw [show D2M8K2.u12269 = KTree.node D2M8K2.u12265 (nat_lit 26003168) (nat_lit 3632077801) (nat_lit 0) D2M8K2.u12268 from rfl, totK_node, atot12265, atot12268]
  decide +kernel

theorem arows12276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12276 = true := by
  rw [show D2M8K2.u12276 = KTree.node D2M8K2.u12272 (nat_lit 26013391) (nat_lit 2432819833) (nat_lit 0) D2M8K2.u12275 from rfl, allE_node, arows12272, irow12276, arows12275]
  all_goals rfl

theorem atot12276 : totK PD2M8K2 D2M8K2.u12276 = [710102485730, 2682290070340, 2908409439243, 901732592875, 50662170050, 0, 0, 0] := by
  rw [show D2M8K2.u12276 = KTree.node D2M8K2.u12272 (nat_lit 26013391) (nat_lit 2432819833) (nat_lit 0) D2M8K2.u12275 from rfl, totK_node, atot12272, atot12275]
  decide +kernel

theorem arows12292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12292 = true := by
  rw [show D2M8K2.u12292 = KTree.node D2M8K2.u12288 (nat_lit 26019824) (nat_lit 3770030118) (nat_lit 0) D2M8K2.u12291 from rfl, allE_node, arows12288, irow12292, arows12291]
  all_goals rfl

theorem atot12292 : totK PD2M8K2 D2M8K2.u12292 = [751134355286, 2831075596287, 2940910336479, 678431578152, 22114025844, 0, 0, 0] := by
  rw [show D2M8K2.u12292 = KTree.node D2M8K2.u12288 (nat_lit 26019824) (nat_lit 3770030118) (nat_lit 0) D2M8K2.u12291 from rfl, totK_node, atot12288, atot12291]
  decide +kernel

theorem arows12299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12299 = true := by
  rw [show D2M8K2.u12299 = KTree.node D2M8K2.u12295 (nat_lit 26028073) (nat_lit 1444693573) (nat_lit 0) D2M8K2.u12298 from rfl, allE_node, arows12295, irow12299, arows12298]
  all_goals rfl

theorem atot12299 : totK PD2M8K2 D2M8K2.u12299 = [0, 1140574331882, 3433448829690, 2318628279092, 250864125146, 2410950632, 0, 0] := by
  rw [show D2M8K2.u12299 = KTree.node D2M8K2.u12295 (nat_lit 26028073) (nat_lit 1444693573) (nat_lit 0) D2M8K2.u12298 from rfl, totK_node, atot12295, atot12298]
  decide +kernel

theorem arows12307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12307 = true := by
  rw [show D2M8K2.u12307 = KTree.node D2M8K2.u12303 (nat_lit 26039382) (nat_lit 3327611821) (nat_lit 0) D2M8K2.u12306 from rfl, allE_node, arows12303, irow12307, arows12306]
  all_goals rfl

theorem atot12307 : totK PD2M8K2 D2M8K2.u12307 = [182717929658, 1198983844346, 2857845208836, 2386079484599, 458733089327, 16654984284, 0, 0] := by
  rw [show D2M8K2.u12307 = KTree.node D2M8K2.u12303 (nat_lit 26039382) (nat_lit 3327611821) (nat_lit 0) D2M8K2.u12306 from rfl, totK_node, atot12303, atot12306]
  decide +kernel

theorem arows12314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12314 = true := by
  rw [show D2M8K2.u12314 = KTree.node D2M8K2.u12310 (nat_lit 26048850) (nat_lit 3467708363) (nat_lit 0) D2M8K2.u12313 from rfl, allE_node, arows12310, irow12314, arows12313]
  all_goals rfl

theorem atot12314 : totK PD2M8K2 D2M8K2.u12314 = [782533736774, 2817008971909, 2838202128573, 768717401887, 38733515471, 0, 0, 0] := by
  rw [show D2M8K2.u12314 = KTree.node D2M8K2.u12310 (nat_lit 26048850) (nat_lit 3467708363) (nat_lit 0) D2M8K2.u12313 from rfl, totK_node, atot12310, atot12313]
  decide +kernel

theorem arows12323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12323 = true := by
  rw [show D2M8K2.u12323 = KTree.node D2M8K2.u12319 (nat_lit 26055052) (nat_lit 2558424332) (nat_lit 0) D2M8K2.u12322 from rfl, allE_node, arows12319, irow12323, arows12322]
  all_goals rfl

theorem atot12323 : totK PD2M8K2 D2M8K2.u12323 = [801876014153, 2841768560940, 2851715076588, 674813518660, 26300412495, 0, 0, 0] := by
  rw [show D2M8K2.u12323 = KTree.node D2M8K2.u12319 (nat_lit 26055052) (nat_lit 2558424332) (nat_lit 0) D2M8K2.u12322 from rfl, totK_node, atot12319, atot12322]
  decide +kernel

theorem arows12330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12330 = true := by
  rw [show D2M8K2.u12330 = KTree.node D2M8K2.u12326 (nat_lit 26065264) (nat_lit 3364724940) (nat_lit 0) D2M8K2.u12329 from rfl, allE_node, arows12326, irow12330, arows12329]
  all_goals rfl

theorem atot12330 : totK PD2M8K2 D2M8K2.u12330 = [358558880073, 2026518055012, 3209498938503, 1450817967683, 138003148468, 1138244013, 0, 0] := by
  rw [show D2M8K2.u12330 = KTree.node D2M8K2.u12326 (nat_lit 26065264) (nat_lit 3364724940) (nat_lit 0) D2M8K2.u12329 from rfl, totK_node, atot12326, atot12329]
  decide +kernel

theorem arows12338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12338 = true := by
  rw [show D2M8K2.u12338 = KTree.node D2M8K2.u12334 (nat_lit 26075634) (nat_lit 3407810300) (nat_lit 0) D2M8K2.u12337 from rfl, allE_node, arows12334, irow12338, arows12337]
  all_goals rfl

theorem atot12338 : totK PD2M8K2 D2M8K2.u12338 = [0, 1461421362077, 3781032682762, 1847770720401, 111257695312, 0, 0, 0] := by
  rw [show D2M8K2.u12338 = KTree.node D2M8K2.u12334 (nat_lit 26075634) (nat_lit 3407810300) (nat_lit 0) D2M8K2.u12337 from rfl, totK_node, atot12334, atot12337]
  decide +kernel

theorem arows12345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12345 = true := by
  rw [show D2M8K2.u12345 = KTree.node D2M8K2.u12341 (nat_lit 26128860) (nat_lit 3199214335) (nat_lit 0) D2M8K2.u12344 from rfl, allE_node, arows12341, irow12345, arows12344]
  all_goals rfl

theorem atot12345 : totK PD2M8K2 D2M8K2.u12345 = [0, 919082083035, 3197849829996, 2628598775292, 394758960496, 6346264815, 0, 0] := by
  rw [show D2M8K2.u12345 = KTree.node D2M8K2.u12341 (nat_lit 26128860) (nat_lit 3199214335) (nat_lit 0) D2M8K2.u12344 from rfl, totK_node, atot12341, atot12344]
  decide +kernel

theorem arows12355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12355 = true := by
  rw [show D2M8K2.u12355 = KTree.node D2M8K2.u12351 (nat_lit 26139393) (nat_lit 1528565760) (nat_lit 0) D2M8K2.u12354 from rfl, allE_node, arows12351, irow12355, arows12354]
  all_goals rfl

theorem atot12355 : totK PD2M8K2 D2M8K2.u12355 = [0, 831572389193, 2880880990508, 2774918060717, 600541298192, 26167767196, 0, 0] := by
  rw [show D2M8K2.u12355 = KTree.node D2M8K2.u12351 (nat_lit 26139393) (nat_lit 1528565760) (nat_lit 0) D2M8K2.u12354 from rfl, totK_node, atot12351, atot12354]
  decide +kernel

theorem arows12362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12362 = true := by
  rw [show D2M8K2.u12362 = KTree.node D2M8K2.u12358 (nat_lit 26146982) (nat_lit 3924565532) (nat_lit 0) D2M8K2.u12361 from rfl, allE_node, arows12358, irow12362, arows12361]
  all_goals rfl

theorem atot12362 : totK PD2M8K2 D2M8K2.u12362 = [0, 321824156341, 2051652104512, 3263081509871, 1262476175912, 115772565193, 1209030869, 0] := by
  rw [show D2M8K2.u12362 = KTree.node D2M8K2.u12358 (nat_lit 26146982) (nat_lit 3924565532) (nat_lit 0) D2M8K2.u12361 from rfl, totK_node, atot12358, atot12361]
  decide +kernel

theorem arows12370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12370 = true := by
  rw [show D2M8K2.u12370 = KTree.node D2M8K2.u12366 (nat_lit 26162123) (nat_lit 1616317528) (nat_lit 0) D2M8K2.u12369 from rfl, allE_node, arows12366, irow12370, arows12369]
  all_goals rfl

theorem atot12370 : totK PD2M8K2 D2M8K2.u12370 = [0, 188814269997, 2015140807443, 3640970679300, 1208564926863, 51858394026, 0, 0] := by
  rw [show D2M8K2.u12370 = KTree.node D2M8K2.u12366 (nat_lit 26162123) (nat_lit 1616317528) (nat_lit 0) D2M8K2.u12369 from rfl, totK_node, atot12366, atot12369]
  decide +kernel

theorem arows12377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12377 = true := by
  rw [show D2M8K2.u12377 = KTree.node D2M8K2.u12373 (nat_lit 26175904) (nat_lit 2821506518) (nat_lit 0) D2M8K2.u12376 from rfl, allE_node, arows12373, irow12377, arows12376]
  all_goals rfl

theorem atot12377 : totK PD2M8K2 D2M8K2.u12377 = [0, 730660292476, 2732887203668, 2886620522245, 853357509998, 49372004117, 0, 0] := by
  rw [show D2M8K2.u12377 = KTree.node D2M8K2.u12373 (nat_lit 26175904) (nat_lit 2821506518) (nat_lit 0) D2M8K2.u12376 from rfl, totK_node, atot12373, atot12376]
  decide +kernel

theorem arows12386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12386 = true := by
  rw [show D2M8K2.u12386 = KTree.node D2M8K2.u12382 (nat_lit 26182975) (nat_lit 2333953420) (nat_lit 0) D2M8K2.u12385 from rfl, allE_node, arows12382, irow12386, arows12385]
  all_goals rfl

theorem atot12386 : totK PD2M8K2 D2M8K2.u12386 = [0, 881854800712, 3076939988790, 2796082035827, 515490271257, 15920989399, 0, 0] := by
  rw [show D2M8K2.u12386 = KTree.node D2M8K2.u12382 (nat_lit 26182975) (nat_lit 2333953420) (nat_lit 0) D2M8K2.u12385 from rfl, totK_node, atot12382, atot12385]
  decide +kernel

theorem arows12393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12393 = true := by
  rw [show D2M8K2.u12393 = KTree.node D2M8K2.u12389 (nat_lit 26211395) (nat_lit 2332631067) (nat_lit 0) D2M8K2.u12392 from rfl, allE_node, arows12389, irow12393, arows12392]
  all_goals rfl

theorem atot12393 : totK PD2M8K2 D2M8K2.u12393 = [0, 939000056088, 3100368726915, 2671851595989, 481371409758, 11040709493, 0, 0] := by
  rw [show D2M8K2.u12393 = KTree.node D2M8K2.u12389 (nat_lit 26211395) (nat_lit 2332631067) (nat_lit 0) D2M8K2.u12392 from rfl, totK_node, atot12389, atot12392]
  decide +kernel

theorem arows12401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12401 = true := by
  rw [show D2M8K2.u12401 = KTree.node D2M8K2.u12397 (nat_lit 26218058) (nat_lit 3991495440) (nat_lit 0) D2M8K2.u12400 from rfl, allE_node, arows12397, irow12401, arows12400]
  all_goals rfl

theorem atot12401 : totK PD2M8K2 D2M8K2.u12401 = [0, 782653556921, 2851206660809, 2884588385306, 713109929503, 28063716506, 0, 0] := by
  rw [show D2M8K2.u12401 = KTree.node D2M8K2.u12397 (nat_lit 26218058) (nat_lit 3991495440) (nat_lit 0) D2M8K2.u12400 from rfl, totK_node, atot12397, atot12400]
  decide +kernel

theorem arows12408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12408 = true := by
  rw [show D2M8K2.u12408 = KTree.node D2M8K2.u12404 (nat_lit 26228334) (nat_lit 3086096655) (nat_lit 0) D2M8K2.u12407 from rfl, allE_node, arows12404, irow12408, arows12407]
  all_goals rfl

theorem atot12408 : totK PD2M8K2 D2M8K2.u12408 = [0, 908596228002, 3096178336824, 2674588790411, 463995058764, 9861410126, 0, 0] := by
  rw [show D2M8K2.u12408 = KTree.node D2M8K2.u12404 (nat_lit 26228334) (nat_lit 3086096655) (nat_lit 0) D2M8K2.u12407 from rfl, totK_node, atot12404, atot12407]
  decide +kernel

theorem arows12419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12419 = true := by
  rw [show D2M8K2.u12419 = KTree.node D2M8K2.u12415 (nat_lit 26257350) (nat_lit 3783624472) (nat_lit 0) D2M8K2.u12418 from rfl, allE_node, arows12415, irow12419, arows12418]
  all_goals rfl

theorem atot12419 : totK PD2M8K2 D2M8K2.u12419 = [0, 856615280435, 3026707373245, 2824842810111, 566614779014, 16376849850, 0, 0] := by
  rw [show D2M8K2.u12419 = KTree.node D2M8K2.u12415 (nat_lit 26257350) (nat_lit 3783624472) (nat_lit 0) D2M8K2.u12418 from rfl, totK_node, atot12415, atot12418]
  decide +kernel

theorem arows12426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12426 = true := by
  rw [show D2M8K2.u12426 = KTree.node D2M8K2.u12422 (nat_lit 26266842) (nat_lit 3886835312) (nat_lit 0) D2M8K2.u12425 from rfl, allE_node, arows12422, irow12426, arows12425]
  all_goals rfl

theorem atot12426 : totK PD2M8K2 D2M8K2.u12426 = [0, 748912557924, 2865121533084, 2931769266825, 620159268176, 19361296925, 0, 0] := by
  rw [show D2M8K2.u12426 = KTree.node D2M8K2.u12422 (nat_lit 26266842) (nat_lit 3886835312) (nat_lit 0) D2M8K2.u12425 from rfl, totK_node, atot12422, atot12425]
  decide +kernel

theorem arows12434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12434 = true := by
  rw [show D2M8K2.u12434 = KTree.node D2M8K2.u12430 (nat_lit 26295866) (nat_lit 4046875920) (nat_lit 0) D2M8K2.u12433 from rfl, allE_node, arows12430, irow12434, arows12433]
  all_goals rfl

theorem atot12434 : totK PD2M8K2 D2M8K2.u12434 = [0, 838087693533, 2972499997917, 2771176730211, 574364233226, 23368668605, 0, 0] := by
  rw [show D2M8K2.u12434 = KTree.node D2M8K2.u12430 (nat_lit 26295866) (nat_lit 4046875920) (nat_lit 0) D2M8K2.u12433 from rfl, totK_node, atot12430, atot12433]
  decide +kernel

theorem arows12441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12441 = true := by
  rw [show D2M8K2.u12441 = KTree.node D2M8K2.u12437 (nat_lit 26302288) (nat_lit 3344895372) (nat_lit 0) D2M8K2.u12440 from rfl, allE_node, arows12437, irow12441, arows12440]
  all_goals rfl

theorem atot12441 : totK PD2M8K2 D2M8K2.u12441 = [0, 838607074068, 2915555618910, 2800098661102, 602673178654, 19465557061, 0, 0] := by
  rw [show D2M8K2.u12441 = KTree.node D2M8K2.u12437 (nat_lit 26302288) (nat_lit 3344895372) (nat_lit 0) D2M8K2.u12440 from rfl, totK_node, atot12437, atot12440]
  decide +kernel

theorem arows12450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12450 = true := by
  rw [show D2M8K2.u12450 = KTree.node D2M8K2.u12446 (nat_lit 26308960) (nat_lit 2165692855) (nat_lit 0) D2M8K2.u12449 from rfl, allE_node, arows12446, irow12450, arows12449]
  all_goals rfl

theorem atot12450 : totK PD2M8K2 D2M8K2.u12450 = [0, 444116253521, 2278742581235, 3210731676407, 1083527719826, 94667357847, 1138244013, 0] := by
  rw [show D2M8K2.u12450 = KTree.node D2M8K2.u12446 (nat_lit 26308960) (nat_lit 2165692855) (nat_lit 0) D2M8K2.u12449 from rfl, totK_node, atot12446, atot12449]
  decide +kernel

theorem arows12457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12457 = true := by
  rw [show D2M8K2.u12457 = KTree.node D2M8K2.u12453 (nat_lit 26321675) (nat_lit 1826652505) (nat_lit 0) D2M8K2.u12456 from rfl, allE_node, arows12453, irow12457, arows12456]
  all_goals rfl

theorem atot12457 : totK PD2M8K2 D2M8K2.u12457 = [0, 0, 1503487232199, 3743578186450, 1734154003947, 120172715019, 0, 0] := by
  rw [show D2M8K2.u12457 = KTree.node D2M8K2.u12453 (nat_lit 26321675) (nat_lit 1826652505) (nat_lit 0) D2M8K2.u12456 from rfl, totK_node, atot12453, atot12456]
  decide +kernel

theorem arows12465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12465 = true := by
  rw [show D2M8K2.u12465 = KTree.node D2M8K2.u12461 (nat_lit 26874896) (nat_lit 3496623157) (nat_lit 0) D2M8K2.u12464 from rfl, allE_node, arows12461, irow12465, arows12464]
  all_goals rfl

theorem atot12465 : totK PD2M8K2 D2M8K2.u12465 = [0, 714031255137, 2402266743055, 2604476947325, 1232348622370, 209870664778, 4977114383, 0] := by
  rw [show D2M8K2.u12465 = KTree.node D2M8K2.u12461 (nat_lit 26874896) (nat_lit 3496623157) (nat_lit 0) D2M8K2.u12464 from rfl, totK_node, atot12461, atot12464]
  decide +kernel

theorem arows12472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12472 = true := by
  rw [show D2M8K2.u12472 = KTree.node D2M8K2.u12468 (nat_lit 26885332) (nat_lit 2629978753) (nat_lit 0) D2M8K2.u12471 from rfl, allE_node, arows12468, irow12472, arows12471]
  all_goals rfl

theorem atot12472 : totK PD2M8K2 D2M8K2.u12472 = [0, 803592765460, 2833742367670, 2800354643851, 650830028045, 26300412495, 0, 0] := by
  rw [show D2M8K2.u12472 = KTree.node D2M8K2.u12468 (nat_lit 26885332) (nat_lit 2629978753) (nat_lit 0) D2M8K2.u12471 from rfl, totK_node, atot12468, atot12471]
  decide +kernel

theorem arows12482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12482 = true := by
  rw [show D2M8K2.u12482 = KTree.node D2M8K2.u12478 (nat_lit 26892009) (nat_lit 1704867559) (nat_lit 0) D2M8K2.u12481 from rfl, allE_node, arows12478, irow12482, arows12481]
  all_goals rfl

theorem atot12482 : totK PD2M8K2 D2M8K2.u12482 = [0, 579315562642, 2581152411061, 3096809530465, 823612068074, 36640207665, 0, 0] := by
  rw [show D2M8K2.u12482 = KTree.node D2M8K2.u12478 (nat_lit 26892009) (nat_lit 1704867559) (nat_lit 0) D2M8K2.u12481 from rfl, totK_node, atot12478, atot12481]
  decide +kernel

theorem arows12489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12489 = true := by
  rw [show D2M8K2.u12489 = KTree.node D2M8K2.u12485 (nat_lit 26902323) (nat_lit 2459260658) (nat_lit 0) D2M8K2.u12488 from rfl, allE_node, arows12485, irow12489, arows12488]
  all_goals rfl

theorem atot12489 : totK PD2M8K2 D2M8K2.u12489 = [0, 0, 1215166213801, 3538519565800, 2070307177048, 209404198601, 1369150432, 0] := by
  rw [show D2M8K2.u12489 = KTree.node D2M8K2.u12485 (nat_lit 26902323) (nat_lit 2459260658) (nat_lit 0) D2M8K2.u12488 from rfl, totK_node, atot12485, atot12488]
  decide +kernel

theorem arows12497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12497 = true := by
  rw [show D2M8K2.u12497 = KTree.node D2M8K2.u12493 (nat_lit 26957022) (nat_lit 3899580057) (nat_lit 0) D2M8K2.u12496 from rfl, allE_node, arows12493, irow12497, arows12496]
  all_goals rfl

theorem atot12497 : totK PD2M8K2 D2M8K2.u12497 = [0, 561308140519, 2456849629356, 3114957648788, 974513163150, 46238259661, 0, 0] := by
  rw [show D2M8K2.u12497 = KTree.node D2M8K2.u12493 (nat_lit 26957022) (nat_lit 3899580057) (nat_lit 0) D2M8K2.u12496 from rfl, totK_node, atot12493, atot12496]
  decide +kernel

theorem arows12504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12504 = true := by
  rw [show D2M8K2.u12504 = KTree.node D2M8K2.u12500 (nat_lit 26964396) (nat_lit 3132990583) (nat_lit 0) D2M8K2.u12503 from rfl, allE_node, arows12500, irow12504, arows12503]
  all_goals rfl

theorem atot12504 : totK PD2M8K2 D2M8K2.u12504 = [0, 791134464069, 2831392880065, 2831415153736, 744393209355, 29554002251, 0, 0] := by
  rw [show D2M8K2.u12504 = KTree.node D2M8K2.u12500 (nat_lit 26964396) (nat_lit 3132990583) (nat_lit 0) D2M8K2.u12503 from rfl, totK_node, atot12500, atot12503]
  decide +kernel

theorem arows12513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12513 = true := by
  rw [show D2M8K2.u12513 = KTree.node D2M8K2.u12509 (nat_lit 26974764) (nat_lit 3030253945) (nat_lit 0) D2M8K2.u12512 from rfl, allE_node, arows12509, irow12513, arows12512]
  all_goals rfl

theorem atot12513 : totK PD2M8K2 D2M8K2.u12513 = [0, 630302058830, 2659062331274, 3078189461863, 782571693905, 28770961189, 0, 0] := by
  rw [show D2M8K2.u12513 = KTree.node D2M8K2.u12509 (nat_lit 26974764) (nat_lit 3030253945) (nat_lit 0) D2M8K2.u12512 from rfl, totK_node, atot12509, atot12512]
  decide +kernel

theorem arows12520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12520 = true := by
  rw [show D2M8K2.u12520 = KTree.node D2M8K2.u12516 (nat_lit 26982603) (nat_lit 3740217982) (nat_lit 0) D2M8K2.u12519 from rfl, allE_node, arows12516, irow12520, arows12519]
  all_goals rfl

theorem atot12520 : totK PD2M8K2 D2M8K2.u12520 = [0, 0, 933601627087, 3188238758984, 2485265778598, 409230677983, 14222663156, 0] := by
  rw [show D2M8K2.u12520 = KTree.node D2M8K2.u12516 (nat_lit 26982603) (nat_lit 3740217982) (nat_lit 0) D2M8K2.u12519 from rfl, totK_node, atot12516, atot12519]
  decide +kernel

theorem arows12528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12528 = true := by
  rw [show D2M8K2.u12528 = KTree.node D2M8K2.u12524 (nat_lit 26994918) (nat_lit 2707722544) (nat_lit 0) D2M8K2.u12527 from rfl, allE_node, arows12524, irow12528, arows12527]
  all_goals rfl

theorem atot12528 : totK PD2M8K2 D2M8K2.u12528 = [0, 419052346373, 1813431086096, 2940031667973, 1704713422522, 204949455750, 4574395652, 0] := by
  rw [show D2M8K2.u12528 = KTree.node D2M8K2.u12524 (nat_lit 26994918) (nat_lit 2707722544) (nat_lit 0) D2M8K2.u12527 from rfl, totK_node, atot12524, atot12527]
  decide +kernel

theorem arows12535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12535 = true := by
  rw [show D2M8K2.u12535 = KTree.node D2M8K2.u12531 (nat_lit 27004412) (nat_lit 3357507821) (nat_lit 0) D2M8K2.u12534 from rfl, allE_node, arows12531, irow12535, arows12534]
  all_goals rfl

theorem atot12535 : totK PD2M8K2 D2M8K2.u12535 = [0, 768768800019, 2886164397831, 2927569759068, 676025088896, 19162378116, 0, 0] := by
  rw [show D2M8K2.u12535 = KTree.node D2M8K2.u12531 (nat_lit 27004412) (nat_lit 3357507821) (nat_lit 0) D2M8K2.u12534 from rfl, totK_node, atot12531, atot12534]
  decide +kernel

theorem arows12547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12547 = true := by
  rw [show D2M8K2.u12547 = KTree.node D2M8K2.u12543 (nat_lit 27014068) (nat_lit 3342385926) (nat_lit 0) D2M8K2.u12546 from rfl, allE_node, arows12543, irow12547, arows12546]
  all_goals rfl

theorem atot12547 : totK PD2M8K2 D2M8K2.u12547 = [0, 795429341796, 2913737796323, 2859461321701, 604162616781, 18301866131, 0, 0] := by
  rw [show D2M8K2.u12547 = KTree.node D2M8K2.u12543 (nat_lit 27014068) (nat_lit 3342385926) (nat_lit 0) D2M8K2.u12546 from rfl, totK_node, atot12543, atot12546]
  decide +kernel

theorem arows12554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12554 = true := by
  rw [show D2M8K2.u12554 = KTree.node D2M8K2.u12550 (nat_lit 27021674) (nat_lit 3869971302) (nat_lit 0) D2M8K2.u12553 from rfl, allE_node, arows12550, irow12554, arows12553]
  all_goals rfl

theorem atot12554 : totK PD2M8K2 D2M8K2.u12554 = [0, 0, 1306233388888, 3607966837576, 2044906750823, 180373476101, 1239866073, 0] := by
  rw [show D2M8K2.u12554 = KTree.node D2M8K2.u12550 (nat_lit 27021674) (nat_lit 3869971302) (nat_lit 0) D2M8K2.u12553 from rfl, totK_node, atot12550, atot12553]
  decide +kernel

theorem arows12562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12562 = true := by
  rw [show D2M8K2.u12562 = KTree.node D2M8K2.u12558 (nat_lit 27033866) (nat_lit 4185316874) (nat_lit 0) D2M8K2.u12561 from rfl, allE_node, arows12558, irow12562, arows12561]
  all_goals rfl

theorem atot12562 : totK PD2M8K2 D2M8K2.u12562 = [0, 0, 881797639105, 3109956602454, 2554119090298, 461919908221, 17826068843, 0] := by
  rw [show D2M8K2.u12562 = KTree.node D2M8K2.u12558 (nat_lit 27033866) (nat_lit 4185316874) (nat_lit 0) D2M8K2.u12561 from rfl, totK_node, atot12558, atot12561]
  decide +kernel

theorem arows12569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12569 = true := by
  rw [show D2M8K2.u12569 = KTree.node D2M8K2.u12565 (nat_lit 27043568) (nat_lit 3731953676) (nat_lit 0) D2M8K2.u12568 from rfl, allE_node, arows12565, irow12569, arows12568]
  all_goals rfl

theorem atot12569 : totK PD2M8K2 D2M8K2.u12569 = [0, 852664324323, 2930441772593, 2725624257926, 682113665770, 33420359711, 0, 0] := by
  rw [show D2M8K2.u12569 = KTree.node D2M8K2.u12565 (nat_lit 27043568) (nat_lit 3731953676) (nat_lit 0) D2M8K2.u12568 from rfl, totK_node, atot12565, atot12568]
  decide +kernel

theorem arows12578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12578 = true := by
  rw [show D2M8K2.u12578 = KTree.node D2M8K2.u12574 (nat_lit 27050330) (nat_lit 3344282452) (nat_lit 0) D2M8K2.u12577 from rfl, allE_node, arows12574, irow12578, arows12577]
  all_goals rfl

theorem atot12578 : totK PD2M8K2 D2M8K2.u12578 = [0, 825429389703, 2840448840823, 2801226959719, 659872222575, 26300412495, 0, 0] := by
  rw [show D2M8K2.u12578 = KTree.node D2M8K2.u12574 (nat_lit 27050330) (nat_lit 3344282452) (nat_lit 0) D2M8K2.u12577 from rfl, totK_node, atot12574, atot12577]
  decide +kernel

theorem arows12585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12585 = true := by
  rw [show D2M8K2.u12585 = KTree.node D2M8K2.u12581 (nat_lit 27060610) (nat_lit 4057470378) (nat_lit 0) D2M8K2.u12584 from rfl, allE_node, arows12581, irow12585, arows12584]
  all_goals rfl

theorem atot12585 : totK PD2M8K2 D2M8K2.u12585 = [0, 352446817612, 2016994879998, 3230551899871, 1436146042451, 131243164233, 1138244013, 0] := by
  rw [show D2M8K2.u12585 = KTree.node D2M8K2.u12581 (nat_lit 27060610) (nat_lit 4057470378) (nat_lit 0) D2M8K2.u12584 from rfl, totK_node, atot12581, atot12584]
  decide +kernel

theorem arows12593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12593 = true := by
  rw [show D2M8K2.u12593 = KTree.node D2M8K2.u12589 (nat_lit 27071325) (nat_lit 1370583779) (nat_lit 0) D2M8K2.u12592 from rfl, allE_node, arows12589, irow12593, arows12592]
  all_goals rfl

theorem atot12593 : totK PD2M8K2 D2M8K2.u12593 = [0, 0, 1429139073439, 3751335961652, 1840753803178, 117587355004, 0, 0] := by
  rw [show D2M8K2.u12593 = KTree.node D2M8K2.u12589 (nat_lit 27071325) (nat_lit 1370583779) (nat_lit 0) D2M8K2.u12592 from rfl, totK_node, atot12589, atot12592]
  decide +kernel

theorem arows12600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12600 = true := by
  rw [show D2M8K2.u12600 = KTree.node D2M8K2.u12596 (nat_lit 27083089) (nat_lit 1558578335) (nat_lit 0) D2M8K2.u12599 from rfl, allE_node, arows12596, irow12600, arows12599]
  all_goals rfl

theorem atot12600 : totK PD2M8K2 D2M8K2.u12600 = [0, 822629260889, 2671704443564, 2500779528013, 971293517002, 180068589191, 4977114383, 0] := by
  rw [show D2M8K2.u12600 = KTree.node D2M8K2.u12596 (nat_lit 27083089) (nat_lit 1558578335) (nat_lit 0) D2M8K2.u12599 from rfl, totK_node, atot12596, atot12599]
  decide +kernel

theorem arows12610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12610 = true := by
  rw [show D2M8K2.u12610 = KTree.node D2M8K2.u12606 (nat_lit 27094281) (nat_lit 1884945045) (nat_lit 0) D2M8K2.u12609 from rfl, allE_node, arows12606, irow12610, arows12609]
  all_goals rfl

theorem atot12610 : totK PD2M8K2 D2M8K2.u12610 = [0, 829385582427, 3006427593443, 2846557318911, 541287981249, 10958897529, 0, 0] := by
  rw [show D2M8K2.u12610 = KTree.node D2M8K2.u12606 (nat_lit 27094281) (nat_lit 1884945045) (nat_lit 0) D2M8K2.u12609 from rfl, totK_node, atot12606, atot12609]
  decide +kernel

theorem arows12617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12617 = true := by
  rw [show D2M8K2.u12617 = KTree.node D2M8K2.u12613 (nat_lit 27104361) (nat_lit 1858708879) (nat_lit 0) D2M8K2.u12616 from rfl, allE_node, arows12613, irow12617, arows12616]
  all_goals rfl

theorem atot12617 : totK PD2M8K2 D2M8K2.u12617 = [0, 0, 1247118356636, 3584416943439, 2067388591726, 178368853490, 1310285577, 0] := by
  rw [show D2M8K2.u12617 = KTree.node D2M8K2.u12613 (nat_lit 27104361) (nat_lit 1858708879) (nat_lit 0) D2M8K2.u12616 from rfl, totK_node, atot12613, atot12616]
  decide +kernel

theorem arows12625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12625 = true := by
  rw [show D2M8K2.u12625 = KTree.node D2M8K2.u12621 (nat_lit 27123381) (nat_lit 1733384879) (nat_lit 0) D2M8K2.u12624 from rfl, allE_node, arows12621, irow12625, arows12624]
  all_goals rfl

theorem atot12625 : totK PD2M8K2 D2M8K2.u12625 = [0, 0, 1198958838235, 3499203102892, 2261400829168, 232082136456, 1369150432, 0] := by
  rw [show D2M8K2.u12625 = KTree.node D2M8K2.u12621 (nat_lit 27123381) (nat_lit 1733384879) (nat_lit 0) D2M8K2.u12624 from rfl, totK_node, atot12621, atot12624]
  decide +kernel

theorem arows12632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12632 = true := by
  rw [show D2M8K2.u12632 = KTree.node D2M8K2.u12628 (nat_lit 27134023) (nat_lit 2394825812) (nat_lit 0) D2M8K2.u12631 from rfl, allE_node, arows12628, irow12632, arows12631]
  all_goals rfl

theorem atot12632 : totK PD2M8K2 D2M8K2.u12632 = [0, 0, 857181042475, 2928407772282, 2643412444492, 537011581227, 25984037814, 0] := by
  rw [show D2M8K2.u12632 = KTree.node D2M8K2.u12628 (nat_lit 27134023) (nat_lit 2394825812) (nat_lit 0) D2M8K2.u12631 from rfl, totK_node, atot12628, atot12631]
  decide +kernel

theorem arows12641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12641 = true := by
  rw [show D2M8K2.u12641 = KTree.node D2M8K2.u12637 (nat_lit 27140930) (nat_lit 1946059247) (nat_lit 2056) D2M8K2.u12640 from rfl, allE_node, arows12637, irow12641, arows12640]
  all_goals rfl

theorem atot12641 : totK PD2M8K2 D2M8K2.u12641 = [0, 0, 581144831316, 2692992875727, 3057883171173, 699258585584, 28020332065, 0] := by
  rw [show D2M8K2.u12641 = KTree.node D2M8K2.u12637 (nat_lit 27140930) (nat_lit 1946059247) (nat_lit 2056) D2M8K2.u12640 from rfl, totK_node, atot12637, atot12640]
  decide +kernel

theorem arows12648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12648 = true := by
  rw [show D2M8K2.u12648 = KTree.node D2M8K2.u12644 (nat_lit 27154806) (nat_lit 3827012122) (nat_lit 0) D2M8K2.u12647 from rfl, allE_node, arows12644, irow12648, arows12647]
  all_goals rfl

theorem atot12648 : totK PD2M8K2 D2M8K2.u12648 = [0, 0, 0, 1597252296637, 3687880055729, 1570839402210, 139577861852, 1369150432] := by
  rw [show D2M8K2.u12648 = KTree.node D2M8K2.u12644 (nat_lit 27154806) (nat_lit 3827012122) (nat_lit 0) D2M8K2.u12647 from rfl, totK_node, atot12644, atot12647]
  decide +kernel

theorem arows12656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12656 = true := by
  rw [show D2M8K2.u12656 = KTree.node D2M8K2.u12652 (nat_lit 27209547) (nat_lit 3776241721) (nat_lit 0) D2M8K2.u12655 from rfl, allE_node, arows12652, irow12656, arows12655]
  all_goals rfl

theorem atot12656 : totK PD2M8K2 D2M8K2.u12656 = [0, 0, 1177960221141, 3473007462176, 2295046220987, 235087373136, 1369150432, 0] := by
  rw [show D2M8K2.u12656 = KTree.node D2M8K2.u12652 (nat_lit 27209547) (nat_lit 3776241721) (nat_lit 0) D2M8K2.u12655 from rfl, totK_node, atot12652, atot12655]
  decide +kernel

theorem arows12663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12663 = true := by
  rw [show D2M8K2.u12663 = KTree.node D2M8K2.u12659 (nat_lit 27221265) (nat_lit 1816948210) (nat_lit 0) D2M8K2.u12662 from rfl, allE_node, arows12659, irow12663, arows12662]
  all_goals rfl

theorem atot12663 : totK PD2M8K2 D2M8K2.u12663 = [0, 0, 948923579745, 3061219969548, 2606434945555, 491873830578, 17966996581, 0] := by
  rw [show D2M8K2.u12663 = KTree.node D2M8K2.u12659 (nat_lit 27221265) (nat_lit 1816948210) (nat_lit 0) D2M8K2.u12662 from rfl, totK_node, atot12659, atot12662]
  decide +kernel

theorem arows12674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12674 = true := by
  rw [show D2M8K2.u12674 = KTree.node D2M8K2.u12670 (nat_lit 27251753) (nat_lit 1733960973) (nat_lit 0) D2M8K2.u12673 from rfl, allE_node, arows12670, irow12674, arows12673]
  all_goals rfl

theorem atot12674 : totK PD2M8K2 D2M8K2.u12674 = [0, 0, 1020345009241, 3316457916821, 2549078687287, 314867795026, 2547901234, 0] := by
  rw [show D2M8K2.u12674 = KTree.node D2M8K2.u12670 (nat_lit 27251753) (nat_lit 1733960973) (nat_lit 0) D2M8K2.u12673 from rfl, totK_node, atot12670, atot12673]
  decide +kernel

theorem arows12681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12681 = true := by
  rw [show D2M8K2.u12681 = KTree.node D2M8K2.u12677 (nat_lit 27263563) (nat_lit 1755175846) (nat_lit 0) D2M8K2.u12680 from rfl, allE_node, arows12677, irow12681, arows12680]
  all_goals rfl

theorem atot12681 : totK PD2M8K2 D2M8K2.u12681 = [0, 0, 1081533113576, 3201270173471, 2418178969382, 419287576119, 16909609931, 0] := by
  rw [show D2M8K2.u12681 = KTree.node D2M8K2.u12677 (nat_lit 27263563) (nat_lit 1755175846) (nat_lit 0) D2M8K2.u12680 from rfl, totK_node, atot12677, atot12680]
  decide +kernel

theorem arows12689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12689 = true := by
  rw [show D2M8K2.u12689 = KTree.node D2M8K2.u12685 (nat_lit 27293408) (nat_lit 3776120356) (nat_lit 0) D2M8K2.u12688 from rfl, allE_node, arows12685, irow12689, arows12688]
  all_goals rfl

theorem atot12689 : totK PD2M8K2 D2M8K2.u12689 = [0, 0, 871678507500, 3137720577135, 2737750481263, 391305701940, 3943030865, 0] := by
  rw [show D2M8K2.u12689 = KTree.node D2M8K2.u12685 (nat_lit 27293408) (nat_lit 3776120356) (nat_lit 0) D2M8K2.u12688 from rfl, totK_node, atot12685, atot12688]
  decide +kernel

theorem arows12696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12696 = true := by
  rw [show D2M8K2.u12696 = KTree.node D2M8K2.u12692 (nat_lit 27301633) (nat_lit 1449219382) (nat_lit 0) D2M8K2.u12695 from rfl, allE_node, arows12692, irow12696, arows12695]
  all_goals rfl

theorem atot12696 : totK PD2M8K2 D2M8K2.u12696 = [0, 0, 844395189330, 2946284171442, 2742229260285, 560997485276, 26099952680, 0] := by
  rw [show D2M8K2.u12696 = KTree.node D2M8K2.u12692 (nat_lit 27301633) (nat_lit 1449219382) (nat_lit 0) D2M8K2.u12695 from rfl, totK_node, atot12692, atot12695]
  decide +kernel

theorem arows12705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12705 = true := by
  rw [show D2M8K2.u12705 = KTree.node D2M8K2.u12701 (nat_lit 27332745) (nat_lit 1867335052) (nat_lit 0) D2M8K2.u12704 from rfl, allE_node, arows12701, irow12705, arows12704]
  all_goals rfl

theorem atot12705 : totK PD2M8K2 D2M8K2.u12705 = [0, 0, 1126255352549, 3332994632212, 2368321454972, 315001894638, 5253160287, 0] := by
  rw [show D2M8K2.u12705 = KTree.node D2M8K2.u12701 (nat_lit 27332745) (nat_lit 1867335052) (nat_lit 0) D2M8K2.u12704 from rfl, totK_node, atot12701, atot12704]
  decide +kernel

theorem arows12712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12712 = true := by
  rw [show D2M8K2.u12712 = KTree.node D2M8K2.u12708 (nat_lit 27417411) (nat_lit 3663281937) (nat_lit 0) D2M8K2.u12711 from rfl, allE_node, arows12708, irow12712, arows12711]
  all_goals rfl

theorem atot12712 : totK PD2M8K2 D2M8K2.u12712 = [0, 515225544756, 2275588353540, 3151735971687, 1293380361188, 82809645829, 0, 0] := by
  rw [show D2M8K2.u12712 = KTree.node D2M8K2.u12708 (nat_lit 27417411) (nat_lit 3663281937) (nat_lit 0) D2M8K2.u12711 from rfl, totK_node, atot12708, atot12711]
  decide +kernel

theorem arows12720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12720 = true := by
  rw [show D2M8K2.u12720 = KTree.node D2M8K2.u12716 (nat_lit 27423505) (nat_lit 1521813674) (nat_lit 0) D2M8K2.u12719 from rfl, allE_node, arows12716, irow12720, arows12719]
  all_goals rfl

theorem atot12720 : totK PD2M8K2 D2M8K2.u12720 = [0, 806319442728, 2856521891851, 2871846082994, 647091409379, 23841391238, 0, 0] := by
  rw [show D2M8K2.u12720 = KTree.node D2M8K2.u12716 (nat_lit 27423505) (nat_lit 1521813674) (nat_lit 0) D2M8K2.u12719 from rfl, totK_node, atot12716, atot12719]
  decide +kernel

theorem arows12727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12727 = true := by
  rw [show D2M8K2.u12727 = KTree.node D2M8K2.u12723 (nat_lit 27430488) (nat_lit 2837078626) (nat_lit 0) D2M8K2.u12726 from rfl, allE_node, arows12723, irow12727, arows12726]
  all_goals rfl

theorem atot12727 : totK PD2M8K2 D2M8K2.u12727 = [0, 796198083298, 2914410999701, 2867352813091, 625207120740, 13345996015, 0, 0] := by
  rw [show D2M8K2.u12727 = KTree.node D2M8K2.u12723 (nat_lit 27430488) (nat_lit 2837078626) (nat_lit 0) D2M8K2.u12726 from rfl, totK_node, atot12723, atot12726]
  decide +kernel

theorem arows12737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12737 = true := by
  rw [show D2M8K2.u12737 = KTree.node D2M8K2.u12733 (nat_lit 27440090) (nat_lit 4241602830) (nat_lit 0) D2M8K2.u12736 from rfl, allE_node, arows12733, irow12737, arows12736]
  all_goals rfl

theorem atot12737 : totK PD2M8K2 D2M8K2.u12737 = [0, 0, 866120617083, 2908378947609, 2736708984221, 722760068474, 39831290253, 0] := by
  rw [show D2M8K2.u12737 = KTree.node D2M8K2.u12733 (nat_lit 27440090) (nat_lit 4241602830) (nat_lit 0) D2M8K2.u12736 from rfl, totK_node, atot12733, atot12736]
  decide +kernel

theorem arows12744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12744 = true := by
  rw [show D2M8K2.u12744 = KTree.node D2M8K2.u12740 (nat_lit 27447018) (nat_lit 3807774765) (nat_lit 0) D2M8K2.u12743 from rfl, allE_node, arows12740, irow12744, arows12743]
  all_goals rfl

theorem atot12744 : totK PD2M8K2 D2M8K2.u12744 = [0, 0, 837726794853, 3094707297573, 2802871079778, 463456066299, 7469324921, 0] := by
  rw [show D2M8K2.u12744 = KTree.node D2M8K2.u12740 (nat_lit 27447018) (nat_lit 3807774765) (nat_lit 0) D2M8K2.u12743 from rfl, totK_node, atot12740, atot12743]
  decide +kernel

theorem arows12752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12752 = true := by
  rw [show D2M8K2.u12752 = KTree.node D2M8K2.u12748 (nat_lit 27454371) (nat_lit 2390209665) (nat_lit 0) D2M8K2.u12751 from rfl, allE_node, arows12748, irow12752, arows12751]
  all_goals rfl

theorem atot12752 : totK PD2M8K2 D2M8K2.u12752 = [0, 507981697955, 2005685452098, 2694766496487, 1657909824148, 364543942845, 10717512769, 0] := by
  rw [show D2M8K2.u12752 = KTree.node D2M8K2.u12748 (nat_lit 27454371) (nat_lit 2390209665) (nat_lit 0) D2M8K2.u12751 from rfl, totK_node, atot12748, atot12751]
  decide +kernel

theorem arows12759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12759 = true := by
  rw [show D2M8K2.u12759 = KTree.node D2M8K2.u12755 (nat_lit 27461528) (nat_lit 3491782222) (nat_lit 0) D2M8K2.u12758 from rfl, allE_node, arows12755, irow12759, arows12758]
  all_goals rfl

theorem atot12759 : totK PD2M8K2 D2M8K2.u12759 = [0, 684325422573, 2633710632472, 2936515190422, 915609488828, 50646844051, 0, 0] := by
  rw [show D2M8K2.u12759 = KTree.node D2M8K2.u12755 (nat_lit 27461528) (nat_lit 3491782222) (nat_lit 0) D2M8K2.u12758 from rfl, totK_node, atot12755, atot12758]
  decide +kernel

theorem arows12768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12768 = true := by
  rw [show D2M8K2.u12768 = KTree.node D2M8K2.u12764 (nat_lit 27471865) (nat_lit 1524685871) (nat_lit 0) D2M8K2.u12767 from rfl, allE_node, arows12764, irow12768, arows12767]
  all_goals rfl

theorem atot12768 : totK PD2M8K2 D2M8K2.u12768 = [0, 800359954272, 2889150090652, 2850874295495, 661532573042, 23212727496, 0, 0] := by
  rw [show D2M8K2.u12768 = KTree.node D2M8K2.u12764 (nat_lit 27471865) (nat_lit 1524685871) (nat_lit 0) D2M8K2.u12767 from rfl, totK_node, atot12764, atot12767]
  decide +kernel

theorem arows12775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12775 = true := by
  rw [show D2M8K2.u12775 = KTree.node D2M8K2.u12771 (nat_lit 27482134) (nat_lit 3513824978) (nat_lit 0) D2M8K2.u12774 from rfl, allE_node, arows12771, irow12775, arows12774]
  all_goals rfl

theorem atot12775 : totK PD2M8K2 D2M8K2.u12775 = [0, 0, 1143803655856, 3359226251977, 2261099469547, 362536303365, 13016197374, 0] := by
  rw [show D2M8K2.u12775 = KTree.node D2M8K2.u12771 (nat_lit 27482134) (nat_lit 3513824978) (nat_lit 0) D2M8K2.u12774 from rfl, totK_node, atot12771, atot12774]
  decide +kernel

theorem arows12783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12783 = true := by
  rw [show D2M8K2.u12783 = KTree.node D2M8K2.u12779 (nat_lit 27492803) (nat_lit 2876481568) (nat_lit 0) D2M8K2.u12782 from rfl, allE_node, arows12779, irow12783, arows12782]
  all_goals rfl

theorem atot12783 : totK PD2M8K2 D2M8K2.u12783 = [0, 325011403864, 1744060182509, 3088012592468, 1771716715754, 219730867109, 4574395652, 0] := by
  rw [show D2M8K2.u12783 = KTree.node D2M8K2.u12779 (nat_lit 27492803) (nat_lit 2876481568) (nat_lit 0) D2M8K2.u12782 from rfl, totK_node, atot12779, atot12782]
  decide +kernel

theorem arows12790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12790 = true := by
  rw [show D2M8K2.u12790 = KTree.node D2M8K2.u12786 (nat_lit 27501984) (nat_lit 3394786623) (nat_lit 0) D2M8K2.u12789 from rfl, allE_node, arows12786, irow12790, arows12789]
  all_goals rfl

theorem atot12790 : totK PD2M8K2 D2M8K2.u12790 = [0, 867664408984, 2935890242339, 2733862866459, 708863409216, 37595089999, 0, 0] := by
  rw [show D2M8K2.u12790 = KTree.node D2M8K2.u12786 (nat_lit 27501984) (nat_lit 3394786623) (nat_lit 0) D2M8K2.u12789 from rfl, totK_node, atot12786, atot12789]
  decide +kernel

theorem arows12803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12803 = true := by
  rw [show D2M8K2.u12803 = KTree.node D2M8K2.u12799 (nat_lit 27511537) (nat_lit 1464451013) (nat_lit 0) D2M8K2.u12802 from rfl, allE_node, arows12799, irow12803, arows12802]
  all_goals rfl

theorem atot12803 : totK PD2M8K2 D2M8K2.u12803 = [0, 800520697250, 2883657164151, 2884329591306, 635222284361, 19499939523, 0, 0] := by
  rw [show D2M8K2.u12803 = KTree.node D2M8K2.u12799 (nat_lit 27511537) (nat_lit 1464451013) (nat_lit 0) D2M8K2.u12802 from rfl, totK_node, atot12799, atot12802]
  decide +kernel

theorem arows12810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12810 = true := by
  rw [show D2M8K2.u12810 = KTree.node D2M8K2.u12806 (nat_lit 27520834) (nat_lit 4101008532) (nat_lit 0) D2M8K2.u12809 from rfl, allE_node, arows12806, irow12810, arows12809]
  all_goals rfl

theorem atot12810 : totK PD2M8K2 D2M8K2.u12810 = [0, 0, 1509364148759, 3763204155526, 1835659998486, 119447266993, 0, 0] := by
  rw [show D2M8K2.u12810 = KTree.node D2M8K2.u12806 (nat_lit 27520834) (nat_lit 4101008532) (nat_lit 0) D2M8K2.u12809 from rfl, totK_node, atot12806, atot12809]
  decide +kernel

theorem arows12818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12818 = true := by
  rw [show D2M8K2.u12818 = KTree.node D2M8K2.u12814 (nat_lit 27532233) (nat_lit 1836876593) (nat_lit 0) D2M8K2.u12817 from rfl, allE_node, arows12814, irow12818, arows12817]
  all_goals rfl

theorem atot12818 : totK PD2M8K2 D2M8K2.u12818 = [0, 104114512826, 1033571882506, 2936381798896, 2515423475748, 498677604759, 17826068843, 0] := by
  rw [show D2M8K2.u12818 = KTree.node D2M8K2.u12814 (nat_lit 27532233) (nat_lit 1836876593) (nat_lit 0) D2M8K2.u12817 from rfl, totK_node, atot12814, atot12817]
  decide +kernel

theorem arows12825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12825 = true := by
  rw [show D2M8K2.u12825 = KTree.node D2M8K2.u12821 (nat_lit 27541992) (nat_lit 2601004231) (nat_lit 0) D2M8K2.u12824 from rfl, allE_node, arows12821, irow12825, arows12824]
  all_goals rfl

theorem atot12825 : totK PD2M8K2 D2M8K2.u12825 = [0, 833058102156, 2869408161124, 2761283513859, 755203321875, 38970858654, 0, 0] := by
  rw [show D2M8K2.u12825 = KTree.node D2M8K2.u12821 (nat_lit 27541992) (nat_lit 2601004231) (nat_lit 0) D2M8K2.u12824 from rfl, totK_node, atot12821, atot12824]
  decide +kernel

theorem arows12834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12834 = true := by
  rw [show D2M8K2.u12834 = KTree.node D2M8K2.u12830 (nat_lit 27548234) (nat_lit 4267463172) (nat_lit 0) D2M8K2.u12833 from rfl, allE_node, arows12830, irow12834, arows12833]
  all_goals rfl

theorem atot12834 : totK PD2M8K2 D2M8K2.u12834 = [0, 799941945191, 2847489648288, 2836344560022, 658399515133, 26300412495, 0, 0] := by
  rw [show D2M8K2.u12834 = KTree.node D2M8K2.u12830 (nat_lit 27548234) (nat_lit 4267463172) (nat_lit 0) D2M8K2.u12833 from rfl, totK_node, atot12830, atot12833]
  decide +kernel

theorem arows12841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12841 = true := by
  rw [show D2M8K2.u12841 = KTree.node D2M8K2.u12837 (nat_lit 27558776) (nat_lit 3741770008) (nat_lit 0) D2M8K2.u12840 from rfl, allE_node, arows12837, irow12841, arows12840]
  all_goals rfl

theorem atot12841 : totK PD2M8K2 D2M8K2.u12841 = [0, 301076925428, 2116997263696, 3467887332600, 1262195856833, 74776451858, 0, 0] := by
  rw [show D2M8K2.u12841 = KTree.node D2M8K2.u12837 (nat_lit 27558776) (nat_lit 3741770008) (nat_lit 0) D2M8K2.u12840 from rfl, totK_node, atot12837, atot12840]
  decide +kernel

theorem arows12849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12849 = true := by
  rw [show D2M8K2.u12849 = KTree.node D2M8K2.u12845 (nat_lit 27570222) (nat_lit 3844506042) (nat_lit 0) D2M8K2.u12848 from rfl, allE_node, arows12845, irow12849, arows12848]
  all_goals rfl

theorem atot12849 : totK PD2M8K2 D2M8K2.u12849 = [0, 22713249043, 1221342391714, 3459862731363, 2187800402045, 274526625851, 4977114383, 0] := by
  rw [show D2M8K2.u12849 = KTree.node D2M8K2.u12845 (nat_lit 27570222) (nat_lit 3844506042) (nat_lit 0) D2M8K2.u12848 from rfl, totK_node, atot12845, atot12848]
  decide +kernel

theorem arows12856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12856 = true := by
  rw [show D2M8K2.u12856 = KTree.node D2M8K2.u12852 (nat_lit 27585316) (nat_lit 3749523361) (nat_lit 0) D2M8K2.u12855 from rfl, allE_node, arows12852, irow12856, arows12855]
  all_goals rfl

theorem atot12856 : totK PD2M8K2 D2M8K2.u12856 = [0, 806609794060, 2785477064137, 2787991387981, 836034595756, 45782046244, 0, 0] := by
  rw [show D2M8K2.u12856 = KTree.node D2M8K2.u12852 (nat_lit 27585316) (nat_lit 3749523361) (nat_lit 0) D2M8K2.u12855 from rfl, totK_node, atot12852, atot12855]
  decide +kernel

theorem arows12866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12866 = true := by
  rw [show D2M8K2.u12866 = KTree.node D2M8K2.u12862 (nat_lit 27592160) (nat_lit 3776799967) (nat_lit 0) D2M8K2.u12865 from rfl, allE_node, arows12862, irow12866, arows12865]
  all_goals rfl

theorem atot12866 : totK PD2M8K2 D2M8K2.u12866 = [0, 832738749245, 2934386022225, 2844336252927, 621462154605, 15855950912, 0, 0] := by
  rw [show D2M8K2.u12866 = KTree.node D2M8K2.u12862 (nat_lit 27592160) (nat_lit 3776799967) (nat_lit 0) D2M8K2.u12865 from rfl, totK_node, atot12862, atot12865]
  decide +kernel

theorem arows12873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12873 = true := by
  rw [show D2M8K2.u12873 = KTree.node D2M8K2.u12869 (nat_lit 27606992) (nat_lit 3612229402) (nat_lit 0) D2M8K2.u12872 from rfl, allE_node, arows12869, irow12873, arows12872]
  all_goals rfl

theorem atot12873 : totK PD2M8K2 D2M8K2.u12873 = [0, 0, 1256119441520, 3532649398060, 2229331235473, 234630015547, 1435164049, 0] := by
  rw [show D2M8K2.u12873 = KTree.node D2M8K2.u12869 (nat_lit 27606992) (nat_lit 3612229402) (nat_lit 0) D2M8K2.u12872 from rfl, totK_node, atot12869, atot12872]
  decide +kernel

theorem arows12881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12881 = true := by
  rw [show D2M8K2.u12881 = KTree.node D2M8K2.u12877 (nat_lit 27618007) (nat_lit 2356197198) (nat_lit 0) D2M8K2.u12880 from rfl, allE_node, arows12877, irow12881, arows12880]
  all_goals rfl

theorem atot12881 : totK PD2M8K2 D2M8K2.u12881 = [0, 347773466219, 1436942906211, 2738240397694, 2242726215092, 422609853088, 11741670991, 0] := by
  rw [show D2M8K2.u12881 = KTree.node D2M8K2.u12877 (nat_lit 27618007) (nat_lit 2356197198) (nat_lit 0) D2M8K2.u12880 from rfl, totK_node, atot12877, atot12880]
  decide +kernel

theorem arows12888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12888 = true := by
  rw [show D2M8K2.u12888 = KTree.node D2M8K2.u12884 (nat_lit 27877585) (nat_lit 1487015166) (nat_lit 0) D2M8K2.u12887 from rfl, allE_node, arows12884, irow12888, arows12887]
  all_goals rfl

theorem atot12888 : totK PD2M8K2 D2M8K2.u12888 = [0, 833639692969, 3039635080357, 2782461224272, 506954736393, 14418877666, 0, 0] := by
  rw [show D2M8K2.u12888 = KTree.node D2M8K2.u12884 (nat_lit 27877585) (nat_lit 1487015166) (nat_lit 0) D2M8K2.u12887 from rfl, totK_node, atot12884, atot12887]
  decide +kernel

theorem arows12897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12897 = true := by
  rw [show D2M8K2.u12897 = KTree.node D2M8K2.u12893 (nat_lit 27884933) (nat_lit 2152066332) (nat_lit 0) D2M8K2.u12896 from rfl, allE_node, arows12893, irow12897, arows12896]
  all_goals rfl

theorem atot12897 : totK PD2M8K2 D2M8K2.u12897 = [0, 794363628629, 2866626648472, 2836130373052, 629281797967, 19499939523, 0, 0] := by
  rw [show D2M8K2.u12897 = KTree.node D2M8K2.u12893 (nat_lit 27884933) (nat_lit 2152066332) (nat_lit 0) D2M8K2.u12896 from rfl, totK_node, atot12893, atot12896]
  decide +kernel

theorem arows12904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12904 = true := by
  rw [show D2M8K2.u12904 = KTree.node D2M8K2.u12900 (nat_lit 27892292) (nat_lit 3102934282) (nat_lit 0) D2M8K2.u12903 from rfl, allE_node, arows12900, irow12904, arows12903]
  all_goals rfl

theorem atot12904 : totK PD2M8K2 D2M8K2.u12904 = [0, 0, 1273674716227, 3567860292952, 1989860525540, 192856707237, 1369150432, 0] := by
  rw [show D2M8K2.u12904 = KTree.node D2M8K2.u12900 (nat_lit 27892292) (nat_lit 3102934282) (nat_lit 0) D2M8K2.u12903 from rfl, totK_node, atot12900, atot12903]
  decide +kernel

theorem arows12912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12912 = true := by
  rw [show D2M8K2.u12912 = KTree.node D2M8K2.u12908 (nat_lit 27907955) (nat_lit 2473942617) (nat_lit 128) D2M8K2.u12911 from rfl, allE_node, arows12908, irow12912, arows12911]
  all_goals rfl

theorem atot12912 : totK PD2M8K2 D2M8K2.u12912 = [0, 442546040397, 2170764301586, 3263974044880, 1266456326093, 66707626739, 0, 0] := by
  rw [show D2M8K2.u12912 = KTree.node D2M8K2.u12908 (nat_lit 27907955) (nat_lit 2473942617) (nat_lit 128) D2M8K2.u12911 from rfl, totK_node, atot12908, atot12911]
  decide +kernel

theorem arows12919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12919 = true := by
  rw [show D2M8K2.u12919 = KTree.node D2M8K2.u12915 (nat_lit 27919208) (nat_lit 2803249319) (nat_lit 0) D2M8K2.u12918 from rfl, allE_node, arows12915, irow12919, arows12918]
  all_goals rfl

theorem atot12919 : totK PD2M8K2 D2M8K2.u12919 = [0, 756441598226, 2777586099237, 2920303726880, 785274443070, 29245827401, 0, 0] := by
  rw [show D2M8K2.u12919 = KTree.node D2M8K2.u12915 (nat_lit 27919208) (nat_lit 2803249319) (nat_lit 0) D2M8K2.u12918 from rfl, totK_node, atot12915, atot12918]
  decide +kernel

theorem arows12930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12930 = true := by
  rw [show D2M8K2.u12930 = KTree.node D2M8K2.u12926 (nat_lit 27926633) (nat_lit 1226836750) (nat_lit 0) D2M8K2.u12929 from rfl, allE_node, arows12926, irow12930, arows12929]
  all_goals rfl

theorem atot12930 : totK PD2M8K2 D2M8K2.u12930 = [0, 801330619180, 2950227705844, 2904241269556, 590077380365, 16094114714, 0, 0] := by
  rw [show D2M8K2.u12930 = KTree.node D2M8K2.u12926 (nat_lit 27926633) (nat_lit 1226836750) (nat_lit 0) D2M8K2.u12929 from rfl, totK_node, atot12926, atot12929]
  decide +kernel

theorem arows12937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12937 = true := by
  rw [show D2M8K2.u12937 = KTree.node D2M8K2.u12933 (nat_lit 27937186) (nat_lit 3963162904) (nat_lit 0) D2M8K2.u12936 from rfl, allE_node, arows12933, irow12937, arows12936]
  all_goals rfl

theorem atot12937 : totK PD2M8K2 D2M8K2.u12937 = [0, 0, 1021764300669, 3261200797971, 2515551581848, 454780472210, 15089109266, 0] := by
  rw [show D2M8K2.u12937 = KTree.node D2M8K2.u12933 (nat_lit 27937186) (nat_lit 3963162904) (nat_lit 0) D2M8K2.u12936 from rfl, totK_node, atot12933, atot12936]
  decide +kernel

theorem arows12945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12945 = true := by
  rw [show D2M8K2.u12945 = KTree.node D2M8K2.u12941 (nat_lit 27945896) (nat_lit 3908741224) (nat_lit 0) D2M8K2.u12944 from rfl, allE_node, arows12941, irow12945, arows12944]
  all_goals rfl

theorem atot12945 : totK PD2M8K2 D2M8K2.u12945 = [0, 0, 1028166501391, 3234227133262, 2588703608666, 411446688935, 6575010705, 0] := by
  rw [show D2M8K2.u12945 = KTree.node D2M8K2.u12941 (nat_lit 27945896) (nat_lit 3908741224) (nat_lit 0) D2M8K2.u12944 from rfl, totK_node, atot12941, atot12944]
  decide +kernel

theorem arows12952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12952 = true := by
  rw [show D2M8K2.u12952 = KTree.node D2M8K2.u12948 (nat_lit 27955060) (nat_lit 3963259066) (nat_lit 0) D2M8K2.u12951 from rfl, allE_node, arows12948, irow12952, arows12951]
  all_goals rfl

theorem atot12952 : totK PD2M8K2 D2M8K2.u12952 = [0, 836818553836, 2902957188202, 2723590159909, 711359238497, 42698063485, 0, 0] := by
  rw [show D2M8K2.u12952 = KTree.node D2M8K2.u12948 (nat_lit 27955060) (nat_lit 3963259066) (nat_lit 0) D2M8K2.u12951 from rfl, totK_node, atot12948, atot12951]
  decide +kernel

theorem arows12961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12961 = true := by
  rw [show D2M8K2.u12961 = KTree.node D2M8K2.u12957 (nat_lit 27961102) (nat_lit 3943772739) (nat_lit 0) D2M8K2.u12960 from rfl, allE_node, arows12957, irow12961, arows12960]
  all_goals rfl

theorem atot12961 : totK PD2M8K2 D2M8K2.u12961 = [0, 866164467545, 2911445276722, 2758188874726, 670097572307, 23830297264, 0, 0] := by
  rw [show D2M8K2.u12961 = KTree.node D2M8K2.u12957 (nat_lit 27961102) (nat_lit 3943772739) (nat_lit 0) D2M8K2.u12960 from rfl, totK_node, atot12957, atot12960]
  decide +kernel

theorem arows12968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12968 = true := by
  rw [show D2M8K2.u12968 = KTree.node D2M8K2.u12964 (nat_lit 27971450) (nat_lit 4284381724) (nat_lit 0) D2M8K2.u12967 from rfl, allE_node, arows12964, irow12968, arows12967]
  all_goals rfl

theorem atot12968 : totK PD2M8K2 D2M8K2.u12968 = [0, 403955624301, 2182345799732, 3281442129594, 1165872652907, 62711405834, 0, 0] := by
  rw [show D2M8K2.u12968 = KTree.node D2M8K2.u12964 (nat_lit 27971450) (nat_lit 4284381724) (nat_lit 0) D2M8K2.u12967 from rfl, totK_node, atot12964, atot12967]
  decide +kernel

theorem arows12976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12976 = true := by
  rw [show D2M8K2.u12976 = KTree.node D2M8K2.u12972 (nat_lit 27980198) (nat_lit 4041768059) (nat_lit 0) D2M8K2.u12975 from rfl, allE_node, arows12972, irow12976, arows12975]
  all_goals rfl

theorem atot12976 : totK PD2M8K2 D2M8K2.u12976 = [0, 0, 968886288559, 3196280019382, 2511627957910, 431541420498, 14222663156, 0] := by
  rw [show D2M8K2.u12976 = KTree.node D2M8K2.u12972 (nat_lit 27980198) (nat_lit 4041768059) (nat_lit 0) D2M8K2.u12975 from rfl, totK_node, atot12972, atot12975]
  decide +kernel

theorem arows12983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12983 = true := by
  rw [show D2M8K2.u12983 = KTree.node D2M8K2.u12979 (nat_lit 27990641) (nat_lit 1734587283) (nat_lit 0) D2M8K2.u12982 from rfl, allE_node, arows12979, irow12983, arows12982]
  all_goals rfl

theorem atot12983 : totK PD2M8K2 D2M8K2.u12983 = [0, 407046338387, 1838543190549, 2939248656021, 1678956296844, 208499181528, 4574395652, 0] := by
  rw [show D2M8K2.u12983 = KTree.node D2M8K2.u12979 (nat_lit 27990641) (nat_lit 1734587283) (nat_lit 0) D2M8K2.u12982 from rfl, totK_node, atot12979, atot12982]
  decide +kernel

theorem arows12993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12993 = true := by
  rw [show D2M8K2.u12993 = KTree.node D2M8K2.u12989 (nat_lit 28040870) (nat_lit 4150634215) (nat_lit 0) D2M8K2.u12992 from rfl, allE_node, arows12989, irow12993, arows12992]
  all_goals rfl

theorem atot12993 : totK PD2M8K2 D2M8K2.u12993 = [0, 844040377578, 2904431952142, 2765585036314, 720629632356, 35985017957, 0, 0] := by
  rw [show D2M8K2.u12993 = KTree.node D2M8K2.u12989 (nat_lit 28040870) (nat_lit 4150634215) (nat_lit 0) D2M8K2.u12992 from rfl, totK_node, atot12989, atot12992]
  decide +kernel

theorem arows13000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13000 = true := by
  rw [show D2M8K2.u13000 = KTree.node D2M8K2.u12996 (nat_lit 28047393) (nat_lit 1682226799) (nat_lit 0) D2M8K2.u12999 from rfl, allE_node, arows12996, irow13000, arows12999]
  all_goals rfl

theorem atot13000 : totK PD2M8K2 D2M8K2.u13000 = [0, 782745509706, 2835903897245, 2859329718446, 677276978300, 27396917599, 0, 0] := by
  rw [show D2M8K2.u13000 = KTree.node D2M8K2.u12996 (nat_lit 28047393) (nat_lit 1682226799) (nat_lit 0) D2M8K2.u12999 from rfl, totK_node, atot12996, atot12999]
  decide +kernel

theorem arows13008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13008 = true := by
  rw [show D2M8K2.u13008 = KTree.node D2M8K2.u13004 (nat_lit 28058222) (nat_lit 2785811114) (nat_lit 0) D2M8K2.u13007 from rfl, allE_node, arows13004, irow13008, arows13007]
  all_goals rfl

theorem atot13008 : totK PD2M8K2 D2M8K2.u13008 = [0, 0, 1419216231369, 3665353116516, 1897414843743, 166389682378, 1138244013, 0] := by
  rw [show D2M8K2.u13008 = KTree.node D2M8K2.u13004 (nat_lit 28058222) (nat_lit 2785811114) (nat_lit 0) D2M8K2.u13007 from rfl, totK_node, atot13004, atot13007]
  decide +kernel

theorem arows13015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13015 = true := by
  rw [show D2M8K2.u13015 = KTree.node D2M8K2.u13011 (nat_lit 28070246) (nat_lit 4124100495) (nat_lit 0) D2M8K2.u13014 from rfl, allE_node, arows13011, irow13015, arows13014]
  all_goals rfl

theorem atot13015 : totK PD2M8K2 D2M8K2.u13015 = [0, 234545227448, 1483717458457, 3149220854314, 1984270129879, 264398271217, 4977114383, 0] := by
  rw [show D2M8K2.u13015 = KTree.node D2M8K2.u13011 (nat_lit 28070246) (nat_lit 4124100495) (nat_lit 0) D2M8K2.u13014 from rfl, totK_node, atot13011, atot13014]
  decide +kernel

theorem arows13024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13024 = true := by
  rw [show D2M8K2.u13024 = KTree.node D2M8K2.u13020 (nat_lit 28081244) (nat_lit 3300649888) (nat_lit 0) D2M8K2.u13023 from rfl, allE_node, arows13020, irow13024, arows13023]
  all_goals rfl

theorem atot13024 : totK PD2M8K2 D2M8K2.u13024 = [0, 790539252173, 2837731018897, 2851952702850, 739128274796, 34947276727, 0, 0] := by
  rw [show D2M8K2.u13024 = KTree.node D2M8K2.u13020 (nat_lit 28081244) (nat_lit 3300649888) (nat_lit 0) D2M8K2.u13023 from rfl, totK_node, atot13020, atot13023]
  decide +kernel

theorem arows13031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13031 = true := by
  rw [show D2M8K2.u13031 = KTree.node D2M8K2.u13027 (nat_lit 28094379) (nat_lit 3677724410) (nat_lit 0) D2M8K2.u13030 from rfl, allE_node, arows13027, irow13031, arows13030]
  all_goals rfl

theorem atot13031 : totK PD2M8K2 D2M8K2.u13031 = [0, 632907176777, 2635912553740, 3045005834266, 844138397790, 36462382936, 0, 0] := by
  rw [show D2M8K2.u13031 = KTree.node D2M8K2.u13027 (nat_lit 28094379) (nat_lit 3677724410) (nat_lit 0) D2M8K2.u13030 from rfl, totK_node, atot13027, atot13030]
  decide +kernel

theorem arows13039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13039 = true := by
  rw [show D2M8K2.u13039 = KTree.node D2M8K2.u13035 (nat_lit 28101733) (nat_lit 1156382649) (nat_lit 0) D2M8K2.u13038 from rfl, allE_node, arows13035, irow13039, arows13038]
  all_goals rfl

theorem atot13039 : totK PD2M8K2 D2M8K2.u13039 = [0, 0, 1118452336624, 3460426421136, 2342198775697, 238347438483, 2385942608, 0] := by
  rw [show D2M8K2.u13039 = KTree.node D2M8K2.u13035 (nat_lit 28101733) (nat_lit 1156382649) (nat_lit 0) D2M8K2.u13038 from rfl, totK_node, atot13035, atot13038]
  decide +kernel

theorem arows13046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13046 = true := by
  rw [show D2M8K2.u13046 = KTree.node D2M8K2.u13042 (nat_lit 28367673) (nat_lit 1870966113) (nat_lit 0) D2M8K2.u13045 from rfl, allE_node, arows13042, irow13046, arows13045]
  all_goals rfl

theorem atot13046 : totK PD2M8K2 D2M8K2.u13046 = [0, 653724168880, 2454970804817, 2794219896059, 1132284828084, 144500246807, 3804183361, 0] := by
  rw [show D2M8K2.u13046 = KTree.node D2M8K2.u13042 (nat_lit 28367673) (nat_lit 1870966113) (nat_lit 0) D2M8K2.u13045 from rfl, totK_node, atot13042, atot13045]
  decide +kernel

theorem arows13058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13058 = true := by
  rw [show D2M8K2.u13058 = KTree.node D2M8K2.u13054 (nat_lit 28378628) (nat_lit 3609900589) (nat_lit 0) D2M8K2.u13057 from rfl, allE_node, arows13054, irow13058, arows13057]
  all_goals rfl

theorem atot13058 : totK PD2M8K2 D2M8K2.u13058 = [0, 845458294439, 2914006674990, 2725799598432, 626620781348, 26300412495, 0, 0] := by
  rw [show D2M8K2.u13058 = KTree.node D2M8K2.u13054 (nat_lit 28378628) (nat_lit 3609900589) (nat_lit 0) D2M8K2.u13057 from rfl, totK_node, atot13054, atot13057]
  decide +kernel

theorem arows13065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13065 = true := by
  rw [show D2M8K2.u13065 = KTree.node D2M8K2.u13061 (nat_lit 28385658) (nat_lit 3909650542) (nat_lit 0) D2M8K2.u13064 from rfl, allE_node, arows13061, irow13065, arows13064]
  all_goals rfl

theorem atot13065 : totK PD2M8K2 D2M8K2.u13065 = [0, 473635009762, 2429270193128, 3240718989918, 942371435064, 40813391089, 0, 0] := by
  rw [show D2M8K2.u13065 = KTree.node D2M8K2.u13061 (nat_lit 28385658) (nat_lit 3909650542) (nat_lit 0) D2M8K2.u13064 from rfl, totK_node, atot13061, atot13064]
  decide +kernel

theorem arows13073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13073 = true := by
  rw [show D2M8K2.u13073 = KTree.node D2M8K2.u13069 (nat_lit 28398360) (nat_lit 2827701208) (nat_lit 0) D2M8K2.u13072 from rfl, allE_node, arows13069, irow13073, arows13072]
  all_goals rfl

theorem atot13073 : totK PD2M8K2 D2M8K2.u13073 = [0, 0, 1258587921506, 3585503495964, 2023393084427, 186994634852, 1369150432, 0] := by
  rw [show D2M8K2.u13073 = KTree.node D2M8K2.u13069 (nat_lit 28398360) (nat_lit 2827701208) (nat_lit 0) D2M8K2.u13072 from rfl, totK_node, atot13069, atot13072]
  decide +kernel

theorem arows13080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13080 = true := by
  rw [show D2M8K2.u13080 = KTree.node D2M8K2.u13076 (nat_lit 28413296) (nat_lit 2970370702) (nat_lit 0) D2M8K2.u13079 from rfl, allE_node, arows13076, irow13080, arows13079]
  all_goals rfl

theorem atot13080 : totK PD2M8K2 D2M8K2.u13080 = [0, 703929212621, 2515638456253, 2960465145685, 1061617361365, 54435779289, 0, 0] := by
  rw [show D2M8K2.u13080 = KTree.node D2M8K2.u13076 (nat_lit 28413296) (nat_lit 2970370702) (nat_lit 0) D2M8K2.u13079 from rfl, totK_node, atot13076, atot13079]
  decide +kernel

theorem arows13089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13089 = true := by
  rw [show D2M8K2.u13089 = KTree.node D2M8K2.u13085 (nat_lit 28420276) (nat_lit 2193280865) (nat_lit 0) D2M8K2.u13088 from rfl, allE_node, arows13085, irow13089, arows13088]
  all_goals rfl

theorem atot13089 : totK PD2M8K2 D2M8K2.u13089 = [0, 869117296482, 2978216073222, 2793940042528, 596995719489, 22956488676, 0, 0] := by
  rw [show D2M8K2.u13089 = KTree.node D2M8K2.u13085 (nat_lit 28420276) (nat_lit 2193280865) (nat_lit 0) D2M8K2.u13088 from rfl, totK_node, atot13085, atot13088]
  decide +kernel

theorem arows13096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13096 = true := by
  rw [show D2M8K2.u13096 = KTree.node D2M8K2.u13092 (nat_lit 28427269) (nat_lit 1069784914) (nat_lit 0) D2M8K2.u13095 from rfl, allE_node, arows13092, irow13096, arows13095]
  all_goals rfl

theorem atot13096 : totK PD2M8K2 D2M8K2.u13096 = [0, 427494810769, 2364264317679, 3304367370027, 1115248029080, 60696629671, 0, 0] := by
  rw [show D2M8K2.u13096 = KTree.node D2M8K2.u13092 (nat_lit 28427269) (nat_lit 1069784914) (nat_lit 0) D2M8K2.u13095 from rfl, totK_node, atot13092, atot13095]
  decide +kernel

theorem arows13104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13104 = true := by
  rw [show D2M8K2.u13104 = KTree.node D2M8K2.u13100 (nat_lit 28439434) (nat_lit 3866912575) (nat_lit 0) D2M8K2.u13103 from rfl, allE_node, arows13100, irow13104, arows13103]
  all_goals rfl

theorem atot13104 : totK PD2M8K2 D2M8K2.u13104 = [0, 0, 844084266811, 3011211938349, 2783026420609, 612421303326, 20396587750, 0] := by
  rw [show D2M8K2.u13104 = KTree.node D2M8K2.u13100 (nat_lit 28439434) (nat_lit 3866912575) (nat_lit 0) D2M8K2.u13103 from rfl, totK_node, atot13100, atot13103]
  decide +kernel

theorem arows13111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13111 = true := by
  rw [show D2M8K2.u13111 = KTree.node D2M8K2.u13107 (nat_lit 28446754) (nat_lit 4167904031) (nat_lit 0) D2M8K2.u13110 from rfl, allE_node, arows13107, irow13111, arows13110]
  all_goals rfl

theorem atot13111 : totK PD2M8K2 D2M8K2.u13111 = [0, 413264604107, 1828067641329, 2938343206917, 1828772036356, 221899621402, 1415142070, 0] := by
  rw [show D2M8K2.u13111 = KTree.node D2M8K2.u13107 (nat_lit 28446754) (nat_lit 4167904031) (nat_lit 0) D2M8K2.u13110 from rfl, totK_node, atot13107, atot13110]
  decide +kernel

theorem arows13121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13121 = true := by
  rw [show D2M8K2.u13121 = KTree.node D2M8K2.u13117 (nat_lit 28496874) (nat_lit 3775134990) (nat_lit 0) D2M8K2.u13120 from rfl, allE_node, arows13117, irow13121, arows13120]
  all_goals rfl

theorem atot13121 : totK PD2M8K2 D2M8K2.u13121 = [0, 798955650258, 2828408957529, 2838113916982, 764544881956, 37260718476, 0, 0] := by
  rw [show D2M8K2.u13121 = KTree.node D2M8K2.u13117 (nat_lit 28496874) (nat_lit 3775134990) (nat_lit 0) D2M8K2.u13120 from rfl, totK_node, atot13117, atot13120]
  decide +kernel

theorem arows13128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13128 = true := by
  rw [show D2M8K2.u13128 = KTree.node D2M8K2.u13124 (nat_lit 28506104) (nat_lit 3506633385) (nat_lit 0) D2M8K2.u13127 from rfl, allE_node, arows13124, irow13128, arows13127]
  all_goals rfl

theorem atot13128 : totK PD2M8K2 D2M8K2.u13128 = [0, 807273109805, 2936204830481, 2865268559507, 595159074660, 18231200220, 0, 0] := by
  rw [show D2M8K2.u13128 = KTree.node D2M8K2.u13124 (nat_lit 28506104) (nat_lit 3506633385) (nat_lit 0) D2M8K2.u13127 from rfl, totK_node, atot13124, atot13127]
  decide +kernel

theorem arows13136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13136 = true := by
  rw [show D2M8K2.u13136 = KTree.node D2M8K2.u13132 (nat_lit 28513269) (nat_lit 1741627740) (nat_lit 0) D2M8K2.u13135 from rfl, allE_node, arows13132, irow13136, arows13135]
  all_goals rfl

theorem atot13136 : totK PD2M8K2 D2M8K2.u13136 = [0, 87861870204, 1449473113963, 3473633056347, 1907287210534, 172468054495, 1239866073, 0] := by
  rw [show D2M8K2.u13136 = KTree.node D2M8K2.u13132 (nat_lit 28513269) (nat_lit 1741627740) (nat_lit 0) D2M8K2.u13135 from rfl, totK_node, atot13132, atot13135]
  decide +kernel

theorem arows13143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13143 = true := by
  rw [show D2M8K2.u13143 = KTree.node D2M8K2.u13139 (nat_lit 28525320) (nat_lit 3453515103) (nat_lit 0) D2M8K2.u13142 from rfl, allE_node, arows13139, irow13143, arows13142]
  all_goals rfl

theorem atot13143 : totK PD2M8K2 D2M8K2.u13143 = [0, 0, 881375467722, 3139365572416, 2633655418837, 443387352212, 14158861562, 0] := by
  rw [show D2M8K2.u13143 = KTree.node D2M8K2.u13139 (nat_lit 28525320) (nat_lit 3453515103) (nat_lit 0) D2M8K2.u13142 from rfl, totK_node, atot13139, atot13142]
  decide +kernel

theorem arows13152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13152 = true := by
  rw [show D2M8K2.u13152 = KTree.node D2M8K2.u13148 (nat_lit 28533962) (nat_lit 3723075960) (nat_lit 0) D2M8K2.u13151 from rfl, allE_node, arows13148, irow13152, arows13151]
  all_goals rfl

theorem atot13152 : totK PD2M8K2 D2M8K2.u13152 = [0, 756484790453, 2727509315713, 2727397693692, 852810424125, 100769652168, 3667207281, 0] := by
  rw [show D2M8K2.u13152 = KTree.node D2M8K2.u13148 (nat_lit 28533962) (nat_lit 3723075960) (nat_lit 0) D2M8K2.u13151 from rfl, totK_node, atot13148, atot13151]
  decide +kernel

theorem arows13159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13159 = true := by
  rw [show D2M8K2.u13159 = KTree.node D2M8K2.u13155 (nat_lit 28540429) (nat_lit 1193301329) (nat_lit 0) D2M8K2.u13158 from rfl, allE_node, arows13155, irow13159, arows13158]
  all_goals rfl

theorem atot13159 : totK PD2M8K2 D2M8K2.u13159 = [0, 766195357094, 2709493867959, 2825372117192, 872886614371, 49024108451, 0, 0] := by
  rw [show D2M8K2.u13159 = KTree.node D2M8K2.u13155 (nat_lit 28540429) (nat_lit 1193301329) (nat_lit 0) D2M8K2.u13158 from rfl, totK_node, atot13155, atot13158]
  decide +kernel

theorem arows13167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13167 = true := by
  rw [show D2M8K2.u13167 = KTree.node D2M8K2.u13163 (nat_lit 28547563) (nat_lit 1607290791) (nat_lit 0) D2M8K2.u13166 from rfl, allE_node, arows13163, irow13167, arows13166]
  all_goals rfl

theorem atot13167 : totK PD2M8K2 D2M8K2.u13167 = [0, 511297306850, 2511701970979, 3244613097749, 883965992032, 36492763016, 0, 0] := by
  rw [show D2M8K2.u13167 = KTree.node D2M8K2.u13163 (nat_lit 28547563) (nat_lit 1607290791) (nat_lit 0) D2M8K2.u13166 from rfl, totK_node, atot13163, atot13166]
  decide +kernel

theorem arows13174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13174 = true := by
  rw [show D2M8K2.u13174 = KTree.node D2M8K2.u13170 (nat_lit 28560402) (nat_lit 3186740192) (nat_lit 0) D2M8K2.u13173 from rfl, allE_node, arows13170, irow13174, arows13173]
  all_goals rfl

theorem atot13174 : totK PD2M8K2 D2M8K2.u13174 = [0, 0, 1248682885478, 3621917703568, 2101516743646, 180190346410, 1138244013, 0] := by
  rw [show D2M8K2.u13174 = KTree.node D2M8K2.u13170 (nat_lit 28560402) (nat_lit 3186740192) (nat_lit 0) D2M8K2.u13173 from rfl, totK_node, atot13170, atot13173]
  decide +kernel

theorem arows13185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13185 = true := by
  rw [show D2M8K2.u13185 = KTree.node D2M8K2.u13181 (nat_lit 28574214) (nat_lit 3804887978) (nat_lit 0) D2M8K2.u13184 from rfl, allE_node, arows13181, irow13185, arows13184]
  all_goals rfl

theorem atot13185 : totK PD2M8K2 D2M8K2.u13185 = [0, 488995250594, 2059786009997, 2869207783167, 1475763127421, 228771927981, 4977114383, 0] := by
  rw [show D2M8K2.u13185 = KTree.node D2M8K2.u13181 (nat_lit 28574214) (nat_lit 3804887978) (nat_lit 0) D2M8K2.u13184 from rfl, totK_node, atot13181, atot13184]
  decide +kernel

theorem arows13192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13192 = true := by
  rw [show D2M8K2.u13192 = KTree.node D2M8K2.u13188 (nat_lit 28584585) (nat_lit 1790562628) (nat_lit 0) D2M8K2.u13191 from rfl, allE_node, arows13188, irow13192, arows13191]
  all_goals rfl

theorem atot13192 : totK PD2M8K2 D2M8K2.u13192 = [0, 741299790902, 2702033773810, 2878821284977, 877791080217, 46898956146, 0, 0] := by
  rw [show D2M8K2.u13192 = KTree.node D2M8K2.u13188 (nat_lit 28584585) (nat_lit 1790562628) (nat_lit 0) D2M8K2.u13191 from rfl, totK_node, atot13188, atot13191]
  decide +kernel

theorem arows13200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13200 = true := by
  rw [show D2M8K2.u13200 = KTree.node D2M8K2.u13196 (nat_lit 28594306) (nat_lit 3904218112) (nat_lit 0) D2M8K2.u13199 from rfl, allE_node, arows13196, irow13200, arows13199]
  all_goals rfl

theorem atot13200 : totK PD2M8K2 D2M8K2.u13200 = [0, 428021878965, 2009541588458, 3108628484199, 1495378862152, 121197151883, 1310285577, 0] := by
  rw [show D2M8K2.u13200 = KTree.node D2M8K2.u13196 (nat_lit 28594306) (nat_lit 3904218112) (nat_lit 0) D2M8K2.u13199 from rfl, totK_node, atot13196, atot13199]
  decide +kernel

theorem arows13207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13207 = true := by
  rw [show D2M8K2.u13207 = KTree.node D2M8K2.u13203 (nat_lit 28606756) (nat_lit 3377534290) (nat_lit 0) D2M8K2.u13206 from rfl, allE_node, arows13203, irow13207, arows13206]
  all_goals rfl

theorem atot13207 : totK PD2M8K2 D2M8K2.u13207 = [0, 0, 1207554392770, 3455950856795, 2277529456915, 279321865929, 4931404646, 0] := by
  rw [show D2M8K2.u13207 = KTree.node D2M8K2.u13203 (nat_lit 28606756) (nat_lit 3377534290) (nat_lit 0) D2M8K2.u13206 from rfl, totK_node, atot13203, atot13206]
  decide +kernel

theorem arows13216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13216 = true := by
  rw [show D2M8K2.u13216 = KTree.node D2M8K2.u13212 (nat_lit 28867753) (nat_lit 1491446707) (nat_lit 0) D2M8K2.u13215 from rfl, allE_node, arows13212, irow13216, arows13215]
  all_goals rfl

theorem atot13216 : totK PD2M8K2 D2M8K2.u13216 = [0, 845908722094, 2946457101104, 2744661585623, 606390156010, 28064973428, 0, 0] := by
  rw [show D2M8K2.u13216 = KTree.node D2M8K2.u13212 (nat_lit 28867753) (nat_lit 1491446707) (nat_lit 0) D2M8K2.u13215 from rfl, totK_node, atot13212, atot13215]
  decide +kernel

theorem arows13223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13223 = true := by
  rw [show D2M8K2.u13223 = KTree.node D2M8K2.u13219 (nat_lit 28878009) (nat_lit 1883336532) (nat_lit 0) D2M8K2.u13222 from rfl, allE_node, arows13219, irow13223, arows13222]
  all_goals rfl

theorem atot13223 : totK PD2M8K2 D2M8K2.u13223 = [0, 834957209315, 3004389425179, 2797454330941, 525944555644, 14347190365, 0, 0] := by
  rw [show D2M8K2.u13223 = KTree.node D2M8K2.u13219 (nat_lit 28878009) (nat_lit 1883336532) (nat_lit 0) D2M8K2.u13222 from rfl, totK_node, atot13219, atot13222]
  decide +kernel

theorem arows13231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13231 = true := by
  rw [show D2M8K2.u13231 = KTree.node D2M8K2.u13227 (nat_lit 28885927) (nat_lit 2011650024) (nat_lit 0) D2M8K2.u13230 from rfl, allE_node, arows13227, irow13231, arows13230]
  all_goals rfl

theorem atot13231 : totK PD2M8K2 D2M8K2.u13231 = [0, 323074992700, 1783221831645, 3145214753133, 1601057714380, 157243800030, 1369150432, 0] := by
  rw [show D2M8K2.u13231 = KTree.node D2M8K2.u13227 (nat_lit 28885927) (nat_lit 2011650024) (nat_lit 0) D2M8K2.u13230 from rfl, totK_node, atot13227, atot13230]
  decide +kernel

theorem arows13238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13238 = true := by
  rw [show D2M8K2.u13238 = KTree.node D2M8K2.u13234 (nat_lit 28899438) (nat_lit 3983372916) (nat_lit 0) D2M8K2.u13237 from rfl, allE_node, arows13234, irow13238, arows13237]
  all_goals rfl

theorem atot13238 : totK PD2M8K2 D2M8K2.u13238 = [0, 127234728902, 1642297427431, 3687992970189, 1578078231287, 71784033525, 0, 0] := by
  rw [show D2M8K2.u13238 = KTree.node D2M8K2.u13234 (nat_lit 28899438) (nat_lit 3983372916) (nat_lit 0) D2M8K2.u13237 from rfl, totK_node, atot13234, atot13237]
  decide +kernel

theorem arows13248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13248 = true := by
  rw [show D2M8K2.u13248 = KTree.node D2M8K2.u13244 (nat_lit 28912780) (nat_lit 3710769412) (nat_lit 0) D2M8K2.u13247 from rfl, allE_node, arows13244, irow13248, arows13247]
  all_goals rfl

theorem atot13248 : totK PD2M8K2 D2M8K2.u13248 = [0, 730412372421, 2683553339740, 2893497697811, 887569861649, 49142669935, 0, 0] := by
  rw [show D2M8K2.u13248 = KTree.node D2M8K2.u13244 (nat_lit 28912780) (nat_lit 3710769412) (nat_lit 0) D2M8K2.u13247 from rfl, totK_node, atot13244, atot13247]
  decide +kernel

theorem arows13255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13255 = true := by
  rw [show D2M8K2.u13255 = KTree.node D2M8K2.u13251 (nat_lit 28919428) (nat_lit 3565929962) (nat_lit 0) D2M8K2.u13254 from rfl, allE_node, arows13251, irow13255, arows13254]
  all_goals rfl

theorem atot13255 : totK PD2M8K2 D2M8K2.u13255 = [0, 839239039437, 3044964578952, 2824521448286, 532304029001, 15837420643, 0, 0] := by
  rw [show D2M8K2.u13255 = KTree.node D2M8K2.u13251 (nat_lit 28919428) (nat_lit 3565929962) (nat_lit 0) D2M8K2.u13254 from rfl, totK_node, atot13251, atot13254]
  decide +kernel

theorem arows13263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13263 = true := by
  rw [show D2M8K2.u13263 = KTree.node D2M8K2.u13259 (nat_lit 28930658) (nat_lit 4114323956) (nat_lit 0) D2M8K2.u13262 from rfl, allE_node, arows13259, irow13263, arows13262]
  all_goals rfl

theorem atot13263 : totK PD2M8K2 D2M8K2.u13263 = [0, 330028431640, 1642451607107, 2874763571826, 1933596974406, 453871452004, 23727080593, 0] := by
  rw [show D2M8K2.u13263 = KTree.node D2M8K2.u13259 (nat_lit 28930658) (nat_lit 4114323956) (nat_lit 0) D2M8K2.u13262 from rfl, totK_node, atot13259, atot13262]
  decide +kernel

theorem arows13270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13270 = true := by
  rw [show D2M8K2.u13270 = KTree.node D2M8K2.u13266 (nat_lit 28937202) (nat_lit 3407810300) (nat_lit 0) D2M8K2.u13269 from rfl, allE_node, arows13266, irow13270, arows13269]
  all_goals rfl

theorem atot13270 : totK PD2M8K2 D2M8K2.u13270 = [0, 0, 922492581000, 3169078754393, 2635974765728, 438177938612, 10378741320, 0] := by
  rw [show D2M8K2.u13270 = KTree.node D2M8K2.u13266 (nat_lit 28937202) (nat_lit 3407810300) (nat_lit 0) D2M8K2.u13269 from rfl, totK_node, atot13266, atot13269]
  decide +kernel

theorem arows13279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13279 = true := by
  rw [show D2M8K2.u13279 = KTree.node D2M8K2.u13275 (nat_lit 28944645) (nat_lit 1443362433) (nat_lit 0) D2M8K2.u13278 from rfl, allE_node, arows13275, irow13279, arows13278]
  all_goals rfl

theorem atot13279 : totK PD2M8K2 D2M8K2.u13279 = [0, 406592456080, 1846076936249, 2968870089419, 1786004091332, 215755462833, 1415142070, 0] := by
  rw [show D2M8K2.u13279 = KTree.node D2M8K2.u13275 (nat_lit 28944645) (nat_lit 1443362433) (nat_lit 0) D2M8K2.u13278 from rfl, totK_node, atot13275, atot13278]
  decide +kernel

theorem arows13286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13286 = true := by
  rw [show D2M8K2.u13286 = KTree.node D2M8K2.u13282 (nat_lit 28953417) (nat_lit 1741890517) (nat_lit 0) D2M8K2.u13285 from rfl, allE_node, arows13282, irow13286, arows13285]
  all_goals rfl

theorem atot13286 : totK PD2M8K2 D2M8K2.u13286 = [0, 857644963171, 2937701513622, 2742133501998, 700289831015, 35981576964, 0, 0] := by
  rw [show D2M8K2.u13286 = KTree.node D2M8K2.u13282 (nat_lit 28953417) (nat_lit 1741890517) (nat_lit 0) D2M8K2.u13285 from rfl, totK_node, atot13282, atot13285]
  decide +kernel

theorem arows13294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13294 = true := by
  rw [show D2M8K2.u13294 = KTree.node D2M8K2.u13290 (nat_lit 28963019) (nat_lit 2734072968) (nat_lit 0) D2M8K2.u13293 from rfl, allE_node, arows13290, irow13294, arows13293]
  all_goals rfl

theorem atot13294 : totK PD2M8K2 D2M8K2.u13294 = [0, 750959639351, 2859109643374, 2939254638707, 637650798878, 19298981496, 0, 0] := by
  rw [show D2M8K2.u13294 = KTree.node D2M8K2.u13290 (nat_lit 28963019) (nat_lit 2734072968) (nat_lit 0) D2M8K2.u13293 from rfl, totK_node, atot13290, atot13293]
  decide +kernel

theorem arows13301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13301 = true := by
  rw [show D2M8K2.u13301 = KTree.node D2M8K2.u13297 (nat_lit 28971170) (nat_lit 3735561971) (nat_lit 0) D2M8K2.u13300 from rfl, allE_node, arows13297, irow13301, arows13300]
  all_goals rfl

theorem atot13301 : totK PD2M8K2 D2M8K2.u13301 = [0, 0, 1273250143220, 3592548914061, 2056408735006, 171958021383, 1206465782, 0] := by
  rw [show D2M8K2.u13301 = KTree.node D2M8K2.u13297 (nat_lit 28971170) (nat_lit 3735561971) (nat_lit 0) D2M8K2.u13300 from rfl, totK_node, atot13297, atot13300]
  decide +kernel

theorem arows13315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13315 = true := by
  rw [show D2M8K2.u13315 = KTree.node D2M8K2.u13311 (nat_lit 28982890) (nat_lit 2510985871) (nat_lit 0) D2M8K2.u13314 from rfl, allE_node, arows13311, irow13315, arows13314]
  all_goals rfl

theorem atot13315 : totK PD2M8K2 D2M8K2.u13315 = [0, 0, 881649448536, 3113272071069, 2555562168011, 451083447488, 17590593026, 0] := by
  rw [show D2M8K2.u13315 = KTree.node D2M8K2.u13311 (nat_lit 28982890) (nat_lit 2510985871) (nat_lit 0) D2M8K2.u13314 from rfl, totK_node, atot13311, atot13314]
  decide +kernel

theorem arows13322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13322 = true := by
  rw [show D2M8K2.u13322 = KTree.node D2M8K2.u13318 (nat_lit 28992865) (nat_lit 664377945) (nat_lit 0) D2M8K2.u13321 from rfl, allE_node, arows13318, irow13322, arows13321]
  all_goals rfl

theorem atot13322 : totK PD2M8K2 D2M8K2.u13322 = [0, 824641558620, 2910042237012, 2771664694106, 678544769121, 31923031227, 0, 0] := by
  rw [show D2M8K2.u13322 = KTree.node D2M8K2.u13318 (nat_lit 28992865) (nat_lit 664377945) (nat_lit 0) D2M8K2.u13321 from rfl, totK_node, atot13318, atot13321]
  decide +kernel

theorem arows13330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13330 = true := by
  rw [show D2M8K2.u13330 = KTree.node D2M8K2.u13326 (nat_lit 29002245) (nat_lit 1470355824) (nat_lit 0) D2M8K2.u13329 from rfl, allE_node, arows13326, irow13330, arows13329]
  all_goals rfl

theorem atot13330 : totK PD2M8K2 D2M8K2.u13330 = [0, 864764364656, 2991539136609, 2776568993878, 592282770969, 19763067536, 0, 0] := by
  rw [show D2M8K2.u13330 = KTree.node D2M8K2.u13326 (nat_lit 29002245) (nat_lit 1470355824) (nat_lit 0) D2M8K2.u13329 from rfl, totK_node, atot13326, atot13329]
  decide +kernel

theorem arows13337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13337 = true := by
  rw [show D2M8K2.u13337 = KTree.node D2M8K2.u13333 (nat_lit 29009798) (nat_lit 2891175930) (nat_lit 0) D2M8K2.u13336 from rfl, allE_node, arows13333, irow13337, arows13336]
  all_goals rfl

theorem atot13337 : totK PD2M8K2 D2M8K2.u13337 = [0, 326274180204, 1822457200877, 3186457286761, 1621357129862, 139894947203, 1239866073, 0] := by
  rw [show D2M8K2.u13337 = KTree.node D2M8K2.u13333 (nat_lit 29009798) (nat_lit 2891175930) (nat_lit 0) D2M8K2.u13336 from rfl, totK_node, atot13333, atot13336]
  decide +kernel

theorem arows13346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13346 = true := by
  rw [show D2M8K2.u13346 = KTree.node D2M8K2.u13342 (nat_lit 29021885) (nat_lit 1189017356) (nat_lit 0) D2M8K2.u13345 from rfl, allE_node, arows13342, irow13346, arows13345]
  all_goals rfl

theorem atot13346 : totK PD2M8K2 D2M8K2.u13346 = [0, 0, 1114620548648, 3364016209202, 2302779755772, 337969080809, 13105450397, 0] := by
  rw [show D2M8K2.u13346 = KTree.node D2M8K2.u13342 (nat_lit 29021885) (nat_lit 1189017356) (nat_lit 0) D2M8K2.u13345 from rfl, totK_node, atot13342, atot13345]
  decide +kernel

theorem arows13353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13353 = true := by
  rw [show D2M8K2.u13353 = KTree.node D2M8K2.u13349 (nat_lit 29031294) (nat_lit 3918539046) (nat_lit 0) D2M8K2.u13352 from rfl, allE_node, arows13349, irow13353, arows13352]
  all_goals rfl

theorem atot13353 : totK PD2M8K2 D2M8K2.u13353 = [0, 683693930759, 2389388112217, 2713673120712, 1192124313479, 168316399224, 4720618446, 0] := by
  rw [show D2M8K2.u13353 = KTree.node D2M8K2.u13349 (nat_lit 29031294) (nat_lit 3918539046) (nat_lit 0) D2M8K2.u13352 from rfl, totK_node, atot13349, atot13352]
  decide +kernel

theorem arows13361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13361 = true := by
  rw [show D2M8K2.u13361 = KTree.node D2M8K2.u13357 (nat_lit 29037701) (nat_lit 2316387304) (nat_lit 0) D2M8K2.u13360 from rfl, allE_node, arows13357, irow13361, arows13360]
  all_goals rfl

theorem atot13361 : totK PD2M8K2 D2M8K2.u13361 = [0, 683846193683, 2650640830141, 2927880803451, 901360206679, 47993443276, 0, 0] := by
  rw [show D2M8K2.u13361 = KTree.node D2M8K2.u13357 (nat_lit 29037701) (nat_lit 2316387304) (nat_lit 0) D2M8K2.u13360 from rfl, totK_node, atot13357, atot13360]
  decide +kernel

theorem arows13368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13368 = true := by
  rw [show D2M8K2.u13368 = KTree.node D2M8K2.u13364 (nat_lit 29044390) (nat_lit 2771684730) (nat_lit 0) D2M8K2.u13367 from rfl, allE_node, arows13364, irow13368, arows13367]
  all_goals rfl

theorem atot13368 : totK PD2M8K2 D2M8K2.u13368 = [0, 762013171564, 2927043409954, 2945404707108, 604012407143, 18231200220, 0, 0] := by
  rw [show D2M8K2.u13368 = KTree.node D2M8K2.u13364 (nat_lit 29044390) (nat_lit 2771684730) (nat_lit 0) D2M8K2.u13367 from rfl, totK_node, atot13364, atot13367]
  decide +kernel

theorem arows13378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13378 = true := by
  rw [show D2M8K2.u13378 = KTree.node D2M8K2.u13374 (nat_lit 29055316) (nat_lit 3685694758) (nat_lit 0) D2M8K2.u13377 from rfl, allE_node, arows13374, irow13378, arows13377]
  all_goals rfl

theorem atot13378 : totK PD2M8K2 D2M8K2.u13378 = [0, 0, 1252578850148, 3606670354216, 2056428203685, 179698215427, 1138244013, 0] := by
  rw [show D2M8K2.u13378 = KTree.node D2M8K2.u13374 (nat_lit 29055316) (nat_lit 3685694758) (nat_lit 0) D2M8K2.u13377 from rfl, totK_node, atot13374, atot13377]
  decide +kernel

theorem arows13385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13385 = true := by
  rw [show D2M8K2.u13385 = KTree.node D2M8K2.u13381 (nat_lit 29066162) (nat_lit 4020524323) (nat_lit 0) D2M8K2.u13384 from rfl, allE_node, arows13381, irow13385, arows13384]
  all_goals rfl

theorem atot13385 : totK PD2M8K2 D2M8K2.u13385 = [0, 0, 1193744842354, 3472775294855, 2193459288633, 274452416541, 4977114383, 0] := by
  rw [show D2M8K2.u13385 = KTree.node D2M8K2.u13381 (nat_lit 29066162) (nat_lit 4020524323) (nat_lit 0) D2M8K2.u13384 from rfl, totK_node, atot13381, atot13384]
  decide +kernel

theorem arows13393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13393 = true := by
  rw [show D2M8K2.u13393 = KTree.node D2M8K2.u13389 (nat_lit 29122057) (nat_lit 1511383944) (nat_lit 0) D2M8K2.u13392 from rfl, allE_node, arows13389, irow13393, arows13392]
  all_goals rfl

theorem atot13393 : totK PD2M8K2 D2M8K2.u13393 = [0, 0, 831283534326, 3066397222318, 2724376056498, 437379246629, 14352600228, 0] := by
  rw [show D2M8K2.u13393 = KTree.node D2M8K2.u13389 (nat_lit 29122057) (nat_lit 1511383944) (nat_lit 0) D2M8K2.u13392 from rfl, totK_node, atot13389, atot13392]
  decide +kernel

theorem arows13400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13400 = true := by
  rw [show D2M8K2.u13400 = KTree.node D2M8K2.u13396 (nat_lit 29129040) (nat_lit 3700418224) (nat_lit 0) D2M8K2.u13399 from rfl, allE_node, arows13396, irow13400, arows13399]
  all_goals rfl

theorem atot13400 : totK PD2M8K2 D2M8K2.u13400 = [0, 0, 740539390066, 2956434549499, 2797835800397, 542568186112, 19433571662, 0] := by
  rw [show D2M8K2.u13400 = KTree.node D2M8K2.u13396 (nat_lit 29129040) (nat_lit 3700418224) (nat_lit 0) D2M8K2.u13399 from rfl, totK_node, atot13396, atot13399]
  decide +kernel

theorem arows13409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13409 = true := by
  rw [show D2M8K2.u13409 = KTree.node D2M8K2.u13405 (nat_lit 29141602) (nat_lit 3751427341) (nat_lit 0) D2M8K2.u13408 from rfl, allE_node, arows13405, irow13409, arows13408]
  all_goals rfl

theorem atot13409 : totK PD2M8K2 D2M8K2.u13409 = [0, 0, 0, 1430964600203, 3668991283663, 1683871156200, 145259245814, 1209030869] := by
  rw [show D2M8K2.u13409 = KTree.node D2M8K2.u13405 (nat_lit 29141602) (nat_lit 3751427341) (nat_lit 0) D2M8K2.u13408 from rfl, totK_node, atot13405, atot13408]
  decide +kernel

theorem arows13416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13416 = true := by
  rw [show D2M8K2.u13416 = KTree.node D2M8K2.u13412 (nat_lit 29159680) (nat_lit 2888758623) (nat_lit 0) D2M8K2.u13415 from rfl, allE_node, arows13412, irow13416, arows13415]
  all_goals rfl

theorem atot13416 : totK PD2M8K2 D2M8K2.u13416 = [0, 0, 743084180336, 2753310952121, 2950210962964, 772804924735, 40250648314, 0] := by
  rw [show D2M8K2.u13416 = KTree.node D2M8K2.u13412 (nat_lit 29159680) (nat_lit 2888758623) (nat_lit 0) D2M8K2.u13415 from rfl, totK_node, atot13412, atot13415]
  decide +kernel

theorem arows13424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13424 = true := by
  rw [show D2M8K2.u13424 = KTree.node D2M8K2.u13420 (nat_lit 29166646) (nat_lit 2898331363) (nat_lit 0) D2M8K2.u13423 from rfl, allE_node, arows13420, irow13424, arows13423]
  all_goals rfl

theorem atot13424 : totK PD2M8K2 D2M8K2.u13424 = [0, 0, 945565599091, 3184674419431, 2618341636220, 447516477916, 19634633155, 0] := by
  rw [show D2M8K2.u13424 = KTree.node D2M8K2.u13420 (nat_lit 29166646) (nat_lit 2898331363) (nat_lit 0) D2M8K2.u13423 from rfl, totK_node, atot13420, atot13423]
  decide +kernel

theorem arows13431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13431 = true := by
  rw [show D2M8K2.u13431 = KTree.node D2M8K2.u13427 (nat_lit 29197109) (nat_lit 2308593483) (nat_lit 0) D2M8K2.u13430 from rfl, allE_node, arows13427, irow13431, arows13430]
  all_goals rfl

theorem atot13431 : totK PD2M8K2 D2M8K2.u13431 = [0, 0, 984018072557, 3287832220026, 2604618888328, 340125791401, 4123500472, 0] := by
  rw [show D2M8K2.u13431 = KTree.node D2M8K2.u13427 (nat_lit 29197109) (nat_lit 2308593483) (nat_lit 0) D2M8K2.u13430 from rfl, totK_node, atot13427, atot13430]
  decide +kernel

theorem arows13442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13442 = true := by
  rw [show D2M8K2.u13442 = KTree.node D2M8K2.u13438 (nat_lit 29204037) (nat_lit 1470583704) (nat_lit 0) D2M8K2.u13441 from rfl, allE_node, arows13438, irow13442, arows13441]
  all_goals rfl

theorem atot13442 : totK PD2M8K2 D2M8K2.u13442 = [0, 0, 863407140813, 2975719820244, 2723467685288, 620503750370, 28063716506, 0] := by
  rw [show D2M8K2.u13442 = KTree.node D2M8K2.u13438 (nat_lit 29204037) (nat_lit 1470583704) (nat_lit 0) D2M8K2.u13441 from rfl, totK_node, atot13438, atot13441]
  decide +kernel

theorem arows13449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13449 = true := by
  rw [show D2M8K2.u13449 = KTree.node D2M8K2.u13445 (nat_lit 29214415) (nat_lit 1030076010) (nat_lit 0) D2M8K2.u13448 from rfl, allE_node, arows13445, irow13449, arows13448]
  all_goals rfl

theorem atot13449 : totK PD2M8K2 D2M8K2.u13449 = [0, 0, 928536745834, 3188517881318, 2607872825137, 375356568681, 6291032136, 0] := by
  rw [show D2M8K2.u13449 = KTree.node D2M8K2.u13445 (nat_lit 29214415) (nat_lit 1030076010) (nat_lit 0) D2M8K2.u13448 from rfl, totK_node, atot13445, atot13448]
  decide +kernel

theorem arows13457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13457 = true := by
  rw [show D2M8K2.u13457 = KTree.node D2M8K2.u13453 (nat_lit 29248232) (nat_lit 3842206317) (nat_lit 0) D2M8K2.u13456 from rfl, allE_node, arows13453, irow13457, arows13456]
  all_goals rfl

theorem atot13457 : totK PD2M8K2 D2M8K2.u13457 = [0, 0, 817459624069, 2958378881756, 2801895474806, 636265941468, 28237008591, 0] := by
  rw [show D2M8K2.u13457 = KTree.node D2M8K2.u13453 (nat_lit 29248232) (nat_lit 3842206317) (nat_lit 0) D2M8K2.u13456 from rfl, totK_node, atot13453, atot13456]
  decide +kernel

theorem arows13464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13464 = true := by
  rw [show D2M8K2.u13464 = KTree.node D2M8K2.u13460 (nat_lit 29255098) (nat_lit 2921039406) (nat_lit 0) D2M8K2.u13463 from rfl, allE_node, arows13460, irow13464, arows13463]
  all_goals rfl

theorem atot13464 : totK PD2M8K2 D2M8K2.u13464 = [0, 0, 1157585651593, 3389107085034, 2298029108402, 296921347220, 4980514959, 0] := by
  rw [show D2M8K2.u13464 = KTree.node D2M8K2.u13460 (nat_lit 29255098) (nat_lit 2921039406) (nat_lit 0) D2M8K2.u13463 from rfl, totK_node, atot13460, atot13463]
  decide +kernel

theorem arows13473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13473 = true := by
  rw [show D2M8K2.u13473 = KTree.node D2M8K2.u13469 (nat_lit 29284921) (nat_lit 741910700) (nat_lit 0) D2M8K2.u13472 from rfl, allE_node, arows13469, irow13473, arows13472]
  all_goals rfl

theorem atot13473 : totK PD2M8K2 D2M8K2.u13473 = [0, 0, 837310986986, 2928815696047, 2763244046796, 597018175920, 25037771093, 0] := by
  rw [show D2M8K2.u13473 = KTree.node D2M8K2.u13469 (nat_lit 29284921) (nat_lit 741910700) (nat_lit 0) D2M8K2.u13472 from rfl, totK_node, atot13469, atot13472]
  decide +kernel

theorem arows13480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13480 = true := by
  rw [show D2M8K2.u13480 = KTree.node D2M8K2.u13476 (nat_lit 29291386) (nat_lit 2443198894) (nat_lit 0) D2M8K2.u13479 from rfl, allE_node, arows13476, irow13480, arows13479]
  all_goals rfl

theorem atot13480 : totK PD2M8K2 D2M8K2.u13480 = [0, 0, 859617124023, 2905015164455, 2725300374181, 593197738441, 26019340052, 0] := by
  rw [show D2M8K2.u13480 = KTree.node D2M8K2.u13476 (nat_lit 29291386) (nat_lit 2443198894) (nat_lit 0) D2M8K2.u13479 from rfl, totK_node, atot13476, atot13479]
  decide +kernel

theorem arows13488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13488 = true := by
  rw [show D2M8K2.u13488 = KTree.node D2M8K2.u13484 (nat_lit 29301768) (nat_lit 3630915925) (nat_lit 0) D2M8K2.u13487 from rfl, allE_node, arows13484, irow13488, arows13487]
  all_goals rfl

theorem atot13488 : totK PD2M8K2 D2M8K2.u13488 = [0, 0, 0, 1486715776128, 3655981662176, 1712475914437, 151196952163, 1138244013] := by
  rw [show D2M8K2.u13488 = KTree.node D2M8K2.u13484 (nat_lit 29301768) (nat_lit 3630915925) (nat_lit 0) D2M8K2.u13487 from rfl, totK_node, atot13484, atot13487]
  decide +kernel

theorem arows13495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13495 = true := by
  rw [show D2M8K2.u13495 = KTree.node D2M8K2.u13491 (nat_lit 29314322) (nat_lit 4099311819) (nat_lit 0) D2M8K2.u13494 from rfl, allE_node, arows13491, irow13495, arows13494]
  all_goals rfl

theorem atot13495 : totK PD2M8K2 D2M8K2.u13495 = [186677387228, 459373490871, 202050743940, 1094868419359, 3009272007605, 1861807888186, 259792500460, 4977114383] := by
  rw [show D2M8K2.u13495 = KTree.node D2M8K2.u13491 (nat_lit 29314322) (nat_lit 4099311819) (nat_lit 0) D2M8K2.u13494 from rfl, totK_node, atot13491, atot13494]
  decide +kernel

theorem arows13505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13505 = true := by
  rw [show D2M8K2.u13505 = KTree.node D2M8K2.u13501 (nat_lit 29867452) (nat_lit 3961990416) (nat_lit 0) D2M8K2.u13504 from rfl, allE_node, arows13501, irow13505, arows13504]
  all_goals rfl

theorem atot13505 : totK PD2M8K2 D2M8K2.u13505 = [862875566395, 3023441971329, 2777317918515, 519744582905, 14418877666, 0, 0, 0] := by
  rw [show D2M8K2.u13505 = KTree.node D2M8K2.u13501 (nat_lit 29867452) (nat_lit 3961990416) (nat_lit 0) D2M8K2.u13504 from rfl, totK_node, atot13501, atot13504]
  decide +kernel

theorem arows13512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13512 = true := by
  rw [show D2M8K2.u13512 = KTree.node D2M8K2.u13508 (nat_lit 29874258) (nat_lit 2633054016) (nat_lit 0) D2M8K2.u13511 from rfl, allE_node, arows13508, irow13512, arows13511]
  all_goals rfl

theorem atot13512 : totK PD2M8K2 D2M8K2.u13512 = [849432373329, 2945045551033, 2742568851392, 564403288110, 18231200220, 0, 0, 0] := by
  rw [show D2M8K2.u13512 = KTree.node D2M8K2.u13508 (nat_lit 29874258) (nat_lit 2633054016) (nat_lit 0) D2M8K2.u13511 from rfl, totK_node, atot13508, atot13511]
  decide +kernel

theorem arows13520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13520 = true := by
  rw [show D2M8K2.u13520 = KTree.node D2M8K2.u13516 (nat_lit 29881261) (nat_lit 1121151367) (nat_lit 0) D2M8K2.u13519 from rfl, allE_node, arows13516, irow13520, arows13519]
  all_goals rfl

theorem atot13520 : totK PD2M8K2 D2M8K2.u13520 = [198165556517, 1616415264078, 3319136049619, 1776235268985, 191998302382, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13520 = KTree.node D2M8K2.u13516 (nat_lit 29881261) (nat_lit 1121151367) (nat_lit 0) D2M8K2.u13519 from rfl, totK_node, atot13516, atot13519]
  decide +kernel

theorem arows13527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13527 = true := by
  rw [show D2M8K2.u13527 = KTree.node D2M8K2.u13523 (nat_lit 29894622) (nat_lit 3954850716) (nat_lit 0) D2M8K2.u13526 from rfl, allE_node, arows13523, irow13527, arows13526]
  all_goals rfl

theorem atot13527 : totK PD2M8K2 D2M8K2.u13527 = [0, 1470584616433, 3761518800884, 1779360615591, 92338634362, 0, 0, 0] := by
  rw [show D2M8K2.u13527 = KTree.node D2M8K2.u13523 (nat_lit 29894622) (nat_lit 3954850716) (nat_lit 0) D2M8K2.u13526 from rfl, totK_node, atot13523, atot13526]
  decide +kernel

theorem arows13536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13536 = true := by
  rw [show D2M8K2.u13536 = KTree.node D2M8K2.u13532 (nat_lit 29946637) (nat_lit 791910879) (nat_lit 0) D2M8K2.u13535 from rfl, allE_node, arows13532, irow13536, arows13535]
  all_goals rfl

theorem atot13536 : totK PD2M8K2 D2M8K2.u13536 = [871832086474, 2928538904817, 2712943369107, 700386125681, 43438729238, 0, 0, 0] := by
  rw [show D2M8K2.u13536 = KTree.node D2M8K2.u13532 (nat_lit 29946637) (nat_lit 791910879) (nat_lit 0) D2M8K2.u13535 from rfl, totK_node, atot13532, atot13535]
  decide +kernel

theorem arows13543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13543 = true := by
  rw [show D2M8K2.u13543 = KTree.node D2M8K2.u13539 (nat_lit 29956745) (nat_lit 1615584201) (nat_lit 0) D2M8K2.u13542 from rfl, allE_node, arows13539, irow13543, arows13542]
  all_goals rfl

theorem atot13543 : totK PD2M8K2 D2M8K2.u13543 = [857663903584, 2965046964951, 2764608390653, 569498925372, 18030242193, 0, 0, 0] := by
  rw [show D2M8K2.u13543 = KTree.node D2M8K2.u13539 (nat_lit 29956745) (nat_lit 1615584201) (nat_lit 0) D2M8K2.u13542 from rfl, totK_node, atot13539, atot13542]
  decide +kernel

theorem arows13551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13551 = true := by
  rw [show D2M8K2.u13551 = KTree.node D2M8K2.u13547 (nat_lit 29963686) (nat_lit 2863888460) (nat_lit 0) D2M8K2.u13550 from rfl, allE_node, arows13547, irow13551, arows13550]
  all_goals rfl

theorem atot13551 : totK PD2M8K2 D2M8K2.u13551 = [250158719299, 1748623872550, 3281670811794, 1714421527934, 164035029430, 1206465782, 0, 0] := by
  rw [show D2M8K2.u13551 = KTree.node D2M8K2.u13547 (nat_lit 29963686) (nat_lit 2863888460) (nat_lit 0) D2M8K2.u13550 from rfl, totK_node, atot13547, atot13550]
  decide +kernel

theorem arows13558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13558 = true := by
  rw [show D2M8K2.u13558 = KTree.node D2M8K2.u13554 (nat_lit 29972568) (nat_lit 2242184059) (nat_lit 0) D2M8K2.u13557 from rfl, allE_node, arows13554, irow13558, arows13557]
  all_goals rfl

theorem atot13558 : totK PD2M8K2 D2M8K2.u13558 = [0, 965519128536, 3174090386890, 2494689221136, 422590786429, 14037798012, 0, 0] := by
  rw [show D2M8K2.u13558 = KTree.node D2M8K2.u13554 (nat_lit 29972568) (nat_lit 2242184059) (nat_lit 0) D2M8K2.u13557 from rfl, totK_node, atot13554, atot13557]
  decide +kernel

theorem arows13570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13570 = true := by
  rw [show D2M8K2.u13570 = KTree.node D2M8K2.u13566 (nat_lit 29985220) (nat_lit 2788612170) (nat_lit 0) D2M8K2.u13569 from rfl, allE_node, arows13566, irow13570, arows13569]
  all_goals rfl

theorem atot13570 : totK PD2M8K2 D2M8K2.u13570 = [665179644339, 2492699579187, 2824596242781, 1080918432493, 128545459476, 3552795014, 0, 0] := by
  rw [show D2M8K2.u13570 = KTree.node D2M8K2.u13566 (nat_lit 29985220) (nat_lit 2788612170) (nat_lit 0) D2M8K2.u13569 from rfl, totK_node, atot13566, atot13569]
  decide +kernel

theorem arows13577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13577 = true := by
  rw [show D2M8K2.u13577 = KTree.node D2M8K2.u13573 (nat_lit 29995855) (nat_lit 2432917385) (nat_lit 0) D2M8K2.u13576 from rfl, allE_node, arows13573, irow13577, arows13576]
  all_goals rfl

theorem atot13577 : totK PD2M8K2 D2M8K2.u13577 = [787687100125, 2751093596441, 2833463727373, 831316485854, 46739014065, 0, 0, 0] := by
  rw [show D2M8K2.u13577 = KTree.node D2M8K2.u13573 (nat_lit 29995855) (nat_lit 2432917385) (nat_lit 0) D2M8K2.u13576 from rfl, totK_node, atot13573, atot13576]
  decide +kernel

theorem arows13585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13585 = true := by
  rw [show D2M8K2.u13585 = KTree.node D2M8K2.u13581 (nat_lit 30002654) (nat_lit 2438429453) (nat_lit 0) D2M8K2.u13584 from rfl, allE_node, arows13581, irow13585, arows13584]
  all_goals rfl

theorem atot13585 : totK PD2M8K2 D2M8K2.u13585 = [531243139844, 2509869403356, 3182417028601, 921334079834, 38106162904, 0, 0, 0] := by
  rw [show D2M8K2.u13585 = KTree.node D2M8K2.u13581 (nat_lit 30002654) (nat_lit 2438429453) (nat_lit 0) D2M8K2.u13584 from rfl, totK_node, atot13581, atot13584]
  decide +kernel

theorem arows13592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13592 = true := by
  rw [show D2M8K2.u13592 = KTree.node D2M8K2.u13588 (nat_lit 30015364) (nat_lit 3382984632) (nat_lit 0) D2M8K2.u13591 from rfl, allE_node, arows13588, irow13592, arows13591]
  all_goals rfl

theorem atot13592 : totK PD2M8K2 D2M8K2.u13592 = [0, 891811501488, 3101685211535, 2654715436344, 458702807245, 14345316470, 0, 0] := by
  rw [show D2M8K2.u13592 = KTree.node D2M8K2.u13588 (nat_lit 30015364) (nat_lit 3382984632) (nat_lit 0) D2M8K2.u13591 from rfl, totK_node, atot13588, atot13591]
  decide +kernel

theorem arows13601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13601 = true := by
  rw [show D2M8K2.u13601 = KTree.node D2M8K2.u13597 (nat_lit 30022434) (nat_lit 2817990344) (nat_lit 0) D2M8K2.u13600 from rfl, allE_node, arows13597, irow13601, arows13600]
  all_goals rfl

theorem atot13601 : totK PD2M8K2 D2M8K2.u13601 = [397873363933, 1742024945835, 2882485821145, 1853803082658, 243692677725, 4720618446, 0, 0] := by
  rw [show D2M8K2.u13601 = KTree.node D2M8K2.u13597 (nat_lit 30022434) (nat_lit 2817990344) (nat_lit 0) D2M8K2.u13600 from rfl, totK_node, atot13597, atot13600]
  decide +kernel

theorem arows13608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13608 = true := by
  rw [show D2M8K2.u13608 = KTree.node D2M8K2.u13604 (nat_lit 30034416) (nat_lit 3618816864) (nat_lit 0) D2M8K2.u13607 from rfl, allE_node, arows13604, irow13608, arows13607]
  all_goals rfl

theorem atot13608 : totK PD2M8K2 D2M8K2.u13608 = [823269030664, 3012640303818, 2810307852585, 523310010347, 14418877666, 0, 0, 0] := by
  rw [show D2M8K2.u13608 = KTree.node D2M8K2.u13604 (nat_lit 30034416) (nat_lit 3618816864) (nat_lit 0) D2M8K2.u13607 from rfl, totK_node, atot13604, atot13607]
  decide +kernel

theorem arows13616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13616 = true := by
  rw [show D2M8K2.u13616 = KTree.node D2M8K2.u13612 (nat_lit 30040956) (nat_lit 2954287894) (nat_lit 0) D2M8K2.u13615 from rfl, allE_node, arows13612, irow13616, arows13615]
  all_goals rfl

theorem atot13616 : totK PD2M8K2 D2M8K2.u13616 = [423568743631, 2282165049441, 3302909930612, 1069204655691, 52390960153, 0, 0, 0] := by
  rw [show D2M8K2.u13616 = KTree.node D2M8K2.u13612 (nat_lit 30040956) (nat_lit 2954287894) (nat_lit 0) D2M8K2.u13615 from rfl, totK_node, atot13612, atot13615]
  decide +kernel

theorem arows13623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13623 = true := by
  rw [show D2M8K2.u13623 = KTree.node D2M8K2.u13619 (nat_lit 30057365) (nat_lit 1961724154) (nat_lit 0) D2M8K2.u13622 from rfl, allE_node, arows13619, irow13623, arows13622]
  all_goals rfl

theorem atot13623 : totK PD2M8K2 D2M8K2.u13623 = [0, 1218653728522, 3530560621330, 2131241870532, 198277630194, 2233351729, 0, 0] := by
  rw [show D2M8K2.u13623 = KTree.node D2M8K2.u13619 (nat_lit 30057365) (nat_lit 1961724154) (nat_lit 0) D2M8K2.u13622 from rfl, totK_node, atot13619, atot13622]
  decide +kernel

theorem arows13633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13633 = true := by
  rw [show D2M8K2.u13633 = KTree.node D2M8K2.u13629 (nat_lit 30069505) (nat_lit 1561674922) (nat_lit 0) D2M8K2.u13632 from rfl, allE_node, arows13629, irow13633, arows13632]
  all_goals rfl

theorem atot13633 : totK PD2M8K2 D2M8K2.u13633 = [770383415551, 2593384842981, 2602055275890, 1089187329212, 181678542642, 3882006667, 0, 0] := by
  rw [show D2M8K2.u13633 = KTree.node D2M8K2.u13629 (nat_lit 30069505) (nat_lit 1561674922) (nat_lit 0) D2M8K2.u13632 from rfl, totK_node, atot13629, atot13632]
  decide +kernel

theorem arows13640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13640 = true := by
  rw [show D2M8K2.u13640 = KTree.node D2M8K2.u13636 (nat_lit 30076518) (nat_lit 1894997884) (nat_lit 0) D2M8K2.u13639 from rfl, allE_node, arows13636, irow13640, arows13639]
  all_goals rfl

theorem atot13640 : totK PD2M8K2 D2M8K2.u13640 = [825814940097, 2881824112879, 2821394063989, 683359235827, 24945851503, 0, 0, 0] := by
  rw [show D2M8K2.u13640 = KTree.node D2M8K2.u13636 (nat_lit 30076518) (nat_lit 1894997884) (nat_lit 0) D2M8K2.u13639 from rfl, totK_node, atot13636, atot13639]
  decide +kernel

theorem arows13648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13648 = true := by
  rw [show D2M8K2.u13648 = KTree.node D2M8K2.u13644 (nat_lit 30086564) (nat_lit 2797008836) (nat_lit 0) D2M8K2.u13647 from rfl, allE_node, arows13644, irow13648, arows13647]
  all_goals rfl

theorem atot13648 : totK PD2M8K2 D2M8K2.u13648 = [442799796658, 2205609366833, 3262692358075, 1232737647096, 65069914974, 0, 0, 0] := by
  rw [show D2M8K2.u13648 = KTree.node D2M8K2.u13644 (nat_lit 30086564) (nat_lit 2797008836) (nat_lit 0) D2M8K2.u13647 from rfl, totK_node, atot13644, atot13647]
  decide +kernel

theorem arows13655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13655 = true := by
  rw [show D2M8K2.u13655 = KTree.node D2M8K2.u13651 (nat_lit 30095381) (nat_lit 2280637084) (nat_lit 0) D2M8K2.u13654 from rfl, allE_node, arows13651, irow13655, arows13654]
  all_goals rfl

theorem atot13655 : totK PD2M8K2 D2M8K2.u13655 = [0, 979829663543, 3182222925325, 2664963469596, 382450669920, 6190125969, 0, 0] := by
  rw [show D2M8K2.u13655 = KTree.node D2M8K2.u13651 (nat_lit 30095381) (nat_lit 2280637084) (nat_lit 0) D2M8K2.u13654 from rfl, totK_node, atot13651, atot13654]
  decide +kernel

theorem arows13664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13664 = true := by
  rw [show D2M8K2.u13664 = KTree.node D2M8K2.u13660 (nat_lit 30105986) (nat_lit 4031739329) (nat_lit 0) D2M8K2.u13663 from rfl, allE_node, arows13660, irow13664, arows13663]
  all_goals rfl

theorem atot13664 : totK PD2M8K2 D2M8K2.u13664 = [0, 810738472801, 2942433464672, 2754520714407, 613005006702, 26682572712, 0, 0] := by
  rw [show D2M8K2.u13664 = KTree.node D2M8K2.u13660 (nat_lit 30105986) (nat_lit 4031739329) (nat_lit 0) D2M8K2.u13663 from rfl, totK_node, atot13660, atot13663]
  decide +kernel

theorem arows13671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13671 = true := by
  rw [show D2M8K2.u13671 = KTree.node D2M8K2.u13667 (nat_lit 30116219) (nat_lit 2870304957) (nat_lit 0) D2M8K2.u13670 from rfl, allE_node, arows13667, irow13671, arows13670]
  all_goals rfl

theorem atot13671 : totK PD2M8K2 D2M8K2.u13671 = [0, 853001134507, 3032454617529, 2769020538594, 478294770511, 14260808441, 0, 0] := by
  rw [show D2M8K2.u13671 = KTree.node D2M8K2.u13667 (nat_lit 30116219) (nat_lit 2870304957) (nat_lit 0) D2M8K2.u13670 from rfl, totK_node, atot13667, atot13670]
  decide +kernel

theorem arows13679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13679 = true := by
  rw [show D2M8K2.u13679 = KTree.node D2M8K2.u13675 (nat_lit 30123090) (nat_lit 2633054016) (nat_lit 0) D2M8K2.u13678 from rfl, allE_node, arows13675, irow13679, arows13678]
  all_goals rfl

theorem atot13679 : totK PD2M8K2 D2M8K2.u13679 = [0, 873239713411, 2959668205732, 2708343954859, 506721840824, 18026911340, 0, 0] := by
  rw [show D2M8K2.u13679 = KTree.node D2M8K2.u13675 (nat_lit 30123090) (nat_lit 2633054016) (nat_lit 0) D2M8K2.u13678 from rfl, totK_node, atot13675, atot13678]
  decide +kernel

theorem arows13686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13686 = true := by
  rw [show D2M8K2.u13686 = KTree.node D2M8K2.u13682 (nat_lit 30130134) (nat_lit 2776089533) (nat_lit 0) D2M8K2.u13685 from rfl, allE_node, arows13682, irow13686, arows13685]
  all_goals rfl

theorem atot13686 : totK PD2M8K2 D2M8K2.u13686 = [0, 182307975947, 1655703163232, 3340814345436, 1667326621317, 188777262403, 1369150432, 0] := by
  rw [show D2M8K2.u13686 = KTree.node D2M8K2.u13682 (nat_lit 30130134) (nat_lit 2776089533) (nat_lit 0) D2M8K2.u13685 from rfl, totK_node, atot13682, atot13685]
  decide +kernel

theorem arows13697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13697 = true := by
  rw [show D2M8K2.u13697 = KTree.node D2M8K2.u13693 (nat_lit 30144001) (nat_lit 1417801816) (nat_lit 0) D2M8K2.u13696 from rfl, allE_node, arows13693, irow13697, arows13696]
  all_goals rfl

theorem atot13697 : totK PD2M8K2 D2M8K2.u13697 = [0, 179595312347, 1826892320398, 3546677664091, 1377561609452, 86117730483, 0, 0] := by
  rw [show D2M8K2.u13697 = KTree.node D2M8K2.u13693 (nat_lit 30144001) (nat_lit 1417801816) (nat_lit 0) D2M8K2.u13696 from rfl, totK_node, atot13693, atot13696]
  decide +kernel

theorem arows13704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13704 = true := by
  rw [show D2M8K2.u13704 = KTree.node D2M8K2.u13700 (nat_lit 30196320) (nat_lit 3261111873) (nat_lit 0) D2M8K2.u13703 from rfl, allE_node, arows13700, irow13704, arows13703]
  all_goals rfl

theorem atot13704 : totK PD2M8K2 D2M8K2.u13704 = [0, 954456302354, 3148515211454, 2685114090536, 438312090795, 6653499497, 0, 0] := by
  rw [show D2M8K2.u13704 = KTree.node D2M8K2.u13700 (nat_lit 30196320) (nat_lit 3261111873) (nat_lit 0) D2M8K2.u13703 from rfl, totK_node, atot13700, atot13703]
  decide +kernel

theorem arows13712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13712 = true := by
  rw [show D2M8K2.u13712 = KTree.node D2M8K2.u13708 (nat_lit 30206638) (nat_lit 2396183262) (nat_lit 0) D2M8K2.u13711 from rfl, allE_node, arows13708, irow13712, arows13711]
  all_goals rfl

theorem atot13712 : totK PD2M8K2 D2M8K2.u13712 = [0, 846463738688, 2981152755288, 2790953878986, 543334833714, 17966996581, 0, 0] := by
  rw [show D2M8K2.u13712 = KTree.node D2M8K2.u13708 (nat_lit 30206638) (nat_lit 2396183262) (nat_lit 0) D2M8K2.u13711 from rfl, totK_node, atot13708, atot13711]
  decide +kernel

theorem arows13719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13719 = true := by
  rw [show D2M8K2.u13719 = KTree.node D2M8K2.u13715 (nat_lit 30234671) (nat_lit 2778802946) (nat_lit 0) D2M8K2.u13718 from rfl, allE_node, arows13715, irow13719, arows13718]
  all_goals rfl

theorem atot13719 : totK PD2M8K2 D2M8K2.u13719 = [0, 749160187650, 2936973098297, 2947955057101, 569169706618, 15053452749, 0, 0] := by
  rw [show D2M8K2.u13719 = KTree.node D2M8K2.u13715 (nat_lit 30234671) (nat_lit 2778802946) (nat_lit 0) D2M8K2.u13718 from rfl, totK_node, atot13715, atot13718]
  decide +kernel

theorem arows13728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13728 = true := by
  rw [show D2M8K2.u13728 = KTree.node D2M8K2.u13724 (nat_lit 30246079) (nat_lit 2372499785) (nat_lit 0) D2M8K2.u13727 from rfl, allE_node, arows13724, irow13728, arows13727]
  all_goals rfl

theorem atot13728 : totK PD2M8K2 D2M8K2.u13728 = [0, 815837498600, 2893487035738, 2833854403957, 612636234690, 19615988614, 0, 0] := by
  rw [show D2M8K2.u13728 = KTree.node D2M8K2.u13724 (nat_lit 30246079) (nat_lit 2372499785) (nat_lit 0) D2M8K2.u13727 from rfl, totK_node, atot13724, atot13727]
  decide +kernel

theorem arows13735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13735 = true := by
  rw [show D2M8K2.u13735 = KTree.node D2M8K2.u13731 (nat_lit 30253034) (nat_lit 4049560188) (nat_lit 0) D2M8K2.u13734 from rfl, allE_node, arows13731, irow13735, arows13734]
  all_goals rfl

theorem atot13735 : totK PD2M8K2 D2M8K2.u13735 = [0, 834418189721, 2956078978175, 2792885192158, 579252841384, 18904996023, 0, 0] := by
  rw [show D2M8K2.u13735 = KTree.node D2M8K2.u13731 (nat_lit 30253034) (nat_lit 4049560188) (nat_lit 0) D2M8K2.u13734 from rfl, totK_node, atot13731, atot13734]
  decide +kernel

theorem arows13743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13743 = true := by
  rw [show D2M8K2.u13743 = KTree.node D2M8K2.u13739 (nat_lit 30284421) (nat_lit 1514933268) (nat_lit 0) D2M8K2.u13742 from rfl, allE_node, arows13739, irow13743, arows13742]
  all_goals rfl

theorem atot13743 : totK PD2M8K2 D2M8K2.u13743 = [0, 798495927930, 2923856032196, 2824952399866, 565519360837, 22585817367, 0, 0] := by
  rw [show D2M8K2.u13743 = KTree.node D2M8K2.u13739 (nat_lit 30284421) (nat_lit 1514933268) (nat_lit 0) D2M8K2.u13742 from rfl, totK_node, atot13739, atot13742]
  decide +kernel

theorem arows13750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13750 = true := by
  rw [show D2M8K2.u13750 = KTree.node D2M8K2.u13746 (nat_lit 30291317) (nat_lit 2378546130) (nat_lit 0) D2M8K2.u13749 from rfl, allE_node, arows13746, irow13750, arows13749]
  all_goals rfl

theorem atot13750 : totK PD2M8K2 D2M8K2.u13750 = [0, 843038927793, 3040596619883, 2788146124577, 478725078100, 9931615220, 0, 0] := by
  rw [show D2M8K2.u13750 = KTree.node D2M8K2.u13746 (nat_lit 30291317) (nat_lit 2378546130) (nat_lit 0) D2M8K2.u13749 from rfl, totK_node, atot13746, atot13749]
  decide +kernel

theorem arows13760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13760 = true := by
  rw [show D2M8K2.u13760 = KTree.node D2M8K2.u13756 (nat_lit 30323212) (nat_lit 3817458740) (nat_lit 0) D2M8K2.u13759 from rfl, allE_node, arows13756, irow13760, arows13759]
  all_goals rfl

theorem atot13760 : totK PD2M8K2 D2M8K2.u13760 = [0, 890442373825, 3003506229588, 2812378058874, 579960099017, 14714084996, 0, 0] := by
  rw [show D2M8K2.u13760 = KTree.node D2M8K2.u13756 (nat_lit 30323212) (nat_lit 3817458740) (nat_lit 0) D2M8K2.u13759 from rfl, totK_node, atot13756, atot13759]
  decide +kernel

theorem arows13767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13767 = true := by
  rw [show D2M8K2.u13767 = KTree.node D2M8K2.u13763 (nat_lit 30333732) (nat_lit 2817681273) (nat_lit 0) D2M8K2.u13766 from rfl, allE_node, arows13763, irow13767, arows13766]
  all_goals rfl

theorem atot13767 : totK PD2M8K2 D2M8K2.u13767 = [49567372496, 793243429807, 2783068557922, 2916389053595, 689187970730, 27090673004, 0, 0] := by
  rw [show D2M8K2.u13767 = KTree.node D2M8K2.u13763 (nat_lit 30333732) (nat_lit 2817681273) (nat_lit 0) D2M8K2.u13766 from rfl, totK_node, atot13763, atot13766]
  decide +kernel

theorem arows13775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13775 = true := by
  rw [show D2M8K2.u13775 = KTree.node D2M8K2.u13771 (nat_lit 30405391) (nat_lit 2418492676) (nat_lit 0) D2M8K2.u13774 from rfl, allE_node, arows13771, irow13775, arows13774]
  all_goals rfl

theorem atot13775 : totK PD2M8K2 D2M8K2.u13775 = [816249905090, 2857539378275, 2811243440660, 779478059538, 39897051795, 0, 0, 0] := by
  rw [show D2M8K2.u13775 = KTree.node D2M8K2.u13771 (nat_lit 30405391) (nat_lit 2418492676) (nat_lit 0) D2M8K2.u13774 from rfl, totK_node, atot13771, atot13774]
  decide +kernel

theorem arows13782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13782 = true := by
  rw [show D2M8K2.u13782 = KTree.node D2M8K2.u13778 (nat_lit 30412033) (nat_lit 1430597759) (nat_lit 0) D2M8K2.u13781 from rfl, allE_node, arows13778, irow13782, arows13781]
  all_goals rfl

theorem atot13782 : totK PD2M8K2 D2M8K2.u13782 = [822285969658, 2914247491059, 2802044129312, 616420303470, 23683401519, 0, 0, 0] := by
  rw [show D2M8K2.u13782 = KTree.node D2M8K2.u13778 (nat_lit 30412033) (nat_lit 1430597759) (nat_lit 0) D2M8K2.u13781 from rfl, totK_node, atot13778, atot13781]
  decide +kernel

theorem arows13791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13791 = true := by
  rw [show D2M8K2.u13791 = KTree.node D2M8K2.u13787 (nat_lit 30418696) (nat_lit 3853227658) (nat_lit 0) D2M8K2.u13790 from rfl, allE_node, arows13787, irow13791, arows13790]
  all_goals rfl

theorem atot13791 : totK PD2M8K2 D2M8K2.u13791 = [425933657684, 2149956585331, 3210585819777, 1366957871182, 138054141456, 10444649207, 0, 0] := by
  rw [show D2M8K2.u13791 = KTree.node D2M8K2.u13787 (nat_lit 30418696) (nat_lit 3853227658) (nat_lit 0) D2M8K2.u13790 from rfl, totK_node, atot13787, atot13790]
  decide +kernel

theorem arows13798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13798 = true := by
  rw [show D2M8K2.u13798 = KTree.node D2M8K2.u13794 (nat_lit 30428142) (nat_lit 3859165384) (nat_lit 0) D2M8K2.u13797 from rfl, allE_node, arows13794, irow13798, arows13797]
  all_goals rfl

theorem atot13798 : totK PD2M8K2 D2M8K2.u13798 = [0, 836602708442, 2825059446373, 2746014542659, 745454765650, 31637093282, 0, 0] := by
  rw [show D2M8K2.u13798 = KTree.node D2M8K2.u13794 (nat_lit 30428142) (nat_lit 3859165384) (nat_lit 0) D2M8K2.u13797 from rfl, totK_node, atot13794, atot13797]
  decide +kernel

theorem arows13806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13806 = true := by
  rw [show D2M8K2.u13806 = KTree.node D2M8K2.u13802 (nat_lit 30435313) (nat_lit 1243681269) (nat_lit 0) D2M8K2.u13805 from rfl, allE_node, arows13802, irow13806, arows13805]
  all_goals rfl

theorem atot13806 : totK PD2M8K2 D2M8K2.u13806 = [0, 824013254940, 3110322143385, 2814511228878, 458170616702, 6634014755, 0, 0] := by
  rw [show D2M8K2.u13806 = KTree.node D2M8K2.u13802 (nat_lit 30435313) (nat_lit 1243681269) (nat_lit 0) D2M8K2.u13805 from rfl, totK_node, atot13802, atot13805]
  decide +kernel

theorem arows13813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13813 = true := by
  rw [show D2M8K2.u13813 = KTree.node D2M8K2.u13809 (nat_lit 30443389) (nat_lit 1204013188) (nat_lit 0) D2M8K2.u13812 from rfl, allE_node, arows13809, irow13813, arows13812]
  all_goals rfl

theorem atot13813 : totK PD2M8K2 D2M8K2.u13813 = [754346683581, 2512352909371, 2493712880445, 1193043464436, 282327362979, 9302370699, 0, 0] := by
  rw [show D2M8K2.u13813 = KTree.node D2M8K2.u13809 (nat_lit 30443389) (nat_lit 1204013188) (nat_lit 0) D2M8K2.u13812 from rfl, totK_node, atot13809, atot13812]
  decide +kernel

theorem arows13826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13826 = true := by
  rw [show D2M8K2.u13826 = KTree.node D2M8K2.u13822 (nat_lit 30449451) (nat_lit 3670238668) (nat_lit 0) D2M8K2.u13825 from rfl, allE_node, arows13822, irow13826, arows13825]
  all_goals rfl

theorem atot13826 : totK PD2M8K2 D2M8K2.u13826 = [820565466379, 2842988213407, 2804748362912, 708689235671, 26374902142, 0, 0, 0] := by
  rw [show D2M8K2.u13826 = KTree.node D2M8K2.u13822 (nat_lit 30449451) (nat_lit 3670238668) (nat_lit 0) D2M8K2.u13825 from rfl, totK_node, atot13822, atot13825]
  decide +kernel

theorem arows13833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13833 = true := by
  rw [show D2M8K2.u13833 = KTree.node D2M8K2.u13829 (nat_lit 30460067) (nat_lit 2848154726) (nat_lit 0) D2M8K2.u13832 from rfl, allE_node, arows13829, irow13833, arows13832]
  all_goals rfl

theorem atot13833 : totK PD2M8K2 D2M8K2.u13833 = [418584527484, 2056044576289, 3130749759216, 1436323534031, 136248602637, 1206465782, 0, 0] := by
  rw [show D2M8K2.u13833 = KTree.node D2M8K2.u13829 (nat_lit 30460067) (nat_lit 2848154726) (nat_lit 0) D2M8K2.u13832 from rfl, totK_node, atot13829, atot13832]
  decide +kernel

theorem arows13841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13841 = true := by
  rw [show D2M8K2.u13841 = KTree.node D2M8K2.u13837 (nat_lit 30469299) (nat_lit 3639192793) (nat_lit 0) D2M8K2.u13840 from rfl, allE_node, arows13837, irow13841, arows13840]
  all_goals rfl

theorem atot13841 : totK PD2M8K2 D2M8K2.u13841 = [0, 1139967824083, 3323674616493, 2331970124632, 379474435694, 13016197374, 0, 0] := by
  rw [show D2M8K2.u13841 = KTree.node D2M8K2.u13837 (nat_lit 30469299) (nat_lit 3639192793) (nat_lit 0) D2M8K2.u13840 from rfl, totK_node, atot13837, atot13840]
  decide +kernel

theorem arows13848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13848 = true := by
  rw [show D2M8K2.u13848 = KTree.node D2M8K2.u13844 (nat_lit 30480029) (nat_lit 2278694330) (nat_lit 0) D2M8K2.u13847 from rfl, allE_node, arows13844, irow13848, arows13847]
  all_goals rfl

theorem atot13848 : totK PD2M8K2 D2M8K2.u13848 = [491803923217, 2048671537223, 2956944228101, 1504966194929, 194910763219, 4574395652, 0, 0] := by
  rw [show D2M8K2.u13848 = KTree.node D2M8K2.u13844 (nat_lit 30480029) (nat_lit 2278694330) (nat_lit 0) D2M8K2.u13847 from rfl, totK_node, atot13844, atot13847]
  decide +kernel

theorem arows13857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13857 = true := by
  rw [show D2M8K2.u13857 = KTree.node D2M8K2.u13853 (nat_lit 30492356) (nat_lit 2437367657) (nat_lit 0) D2M8K2.u13856 from rfl, allE_node, arows13853, irow13857, arows13856]
  all_goals rfl

theorem atot13857 : totK PD2M8K2 D2M8K2.u13857 = [701306638440, 2653860847814, 2909835004088, 909534352264, 50845775260, 0, 0, 0] := by
  rw [show D2M8K2.u13857 = KTree.node D2M8K2.u13853 (nat_lit 30492356) (nat_lit 2437367657) (nat_lit 0) D2M8K2.u13856 from rfl, totK_node, atot13853, atot13856]
  decide +kernel

theorem arows13864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13864 = true := by
  rw [show D2M8K2.u13864 = KTree.node D2M8K2.u13860 (nat_lit 30499323) (nat_lit 3064860362) (nat_lit 0) D2M8K2.u13863 from rfl, allE_node, arows13860, irow13864, arows13863]
  all_goals rfl

theorem atot13864 : totK PD2M8K2 D2M8K2.u13864 = [800933205286, 2918791007836, 2888778860372, 632188909140, 14893202012, 0, 0, 0] := by
  rw [show D2M8K2.u13864 = KTree.node D2M8K2.u13860 (nat_lit 30499323) (nat_lit 3064860362) (nat_lit 0) D2M8K2.u13863 from rfl, totK_node, atot13860, atot13863]
  decide +kernel

theorem arows13872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13872 = true := by
  rw [show D2M8K2.u13872 = KTree.node D2M8K2.u13868 (nat_lit 30507019) (nat_lit 1815681041) (nat_lit 0) D2M8K2.u13871 from rfl, allE_node, arows13868, irow13872, arows13871]
  all_goals rfl

theorem atot13872 : totK PD2M8K2 D2M8K2.u13872 = [0, 1189152204865, 3472629725739, 2292766768853, 238422014497, 1239866073, 0, 0] := by
  rw [show D2M8K2.u13872 = KTree.node D2M8K2.u13868 (nat_lit 30507019) (nat_lit 1815681041) (nat_lit 0) D2M8K2.u13871 from rfl, totK_node, atot13868, atot13871]
  decide +kernel

theorem arows13879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13879 = true := by
  rw [show D2M8K2.u13879 = KTree.node D2M8K2.u13875 (nat_lit 30518576) (nat_lit 3734983225) (nat_lit 0) D2M8K2.u13878 from rfl, allE_node, arows13875, irow13879, arows13878]
  all_goals rfl

theorem atot13879 : totK PD2M8K2 D2M8K2.u13879 = [159085141884, 1128946974984, 2946996633348, 2427605746519, 477600464264, 17826068843, 0, 0] := by
  rw [show D2M8K2.u13879 = KTree.node D2M8K2.u13875 (nat_lit 30518576) (nat_lit 3734983225) (nat_lit 0) D2M8K2.u13878 from rfl, totK_node, atot13875, atot13878]
  decide +kernel

theorem arows13889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13889 = true := by
  rw [show D2M8K2.u13889 = KTree.node D2M8K2.u13885 (nat_lit 30530305) (nat_lit 1573088089) (nat_lit 0) D2M8K2.u13888 from rfl, allE_node, arows13885, irow13889, arows13888]
  all_goals rfl

theorem atot13889 : totK PD2M8K2 D2M8K2.u13889 = [682603923449, 2633770288767, 2931947451746, 920799651980, 50651435456, 0, 0, 0] := by
  rw [show D2M8K2.u13889 = KTree.node D2M8K2.u13885 (nat_lit 30530305) (nat_lit 1573088089) (nat_lit 0) D2M8K2.u13888 from rfl, totK_node, atot13885, atot13888]
  decide +kernel

theorem arows13896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13896 = true := by
  rw [show D2M8K2.u13896 = KTree.node D2M8K2.u13892 (nat_lit 30537222) (nat_lit 3773650675) (nat_lit 0) D2M8K2.u13895 from rfl, allE_node, arows13892, irow13896, arows13895]
  all_goals rfl

theorem atot13896 : totK PD2M8K2 D2M8K2.u13896 = [816595464932, 2972171835288, 2835467470699, 598492583012, 18231200220, 0, 0, 0] := by
  rw [show D2M8K2.u13896 = KTree.node D2M8K2.u13892 (nat_lit 30537222) (nat_lit 3773650675) (nat_lit 0) D2M8K2.u13895 from rfl, totK_node, atot13892, atot13895]
  decide +kernel

theorem arows13904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13904 = true := by
  rw [show D2M8K2.u13904 = KTree.node D2M8K2.u13900 (nat_lit 30552432) (nat_lit 3372027654) (nat_lit 0) D2M8K2.u13903 from rfl, allE_node, arows13900, irow13904, arows13903]
  all_goals rfl

theorem atot13904 : totK PD2M8K2 D2M8K2.u13904 = [0, 1459480833407, 3763713488910, 1880533152147, 124913769922, 0, 0, 0] := by
  rw [show D2M8K2.u13904 = KTree.node D2M8K2.u13900 (nat_lit 30552432) (nat_lit 3372027654) (nat_lit 0) D2M8K2.u13903 from rfl, totK_node, atot13900, atot13903]
  decide +kernel

theorem arows13911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13911 = true := by
  rw [show D2M8K2.u13911 = KTree.node D2M8K2.u13907 (nat_lit 30566426) (nat_lit 3915000491) (nat_lit 0) D2M8K2.u13910 from rfl, allE_node, arows13907, irow13911, arows13910]
  all_goals rfl

theorem atot13911 : totK PD2M8K2 D2M8K2.u13911 = [773699682448, 2521034878635, 2577917902751, 1154370577902, 199346488272, 4977114383, 0, 0] := by
  rw [show D2M8K2.u13911 = KTree.node D2M8K2.u13907 (nat_lit 30566426) (nat_lit 3915000491) (nat_lit 0) D2M8K2.u13910 from rfl, totK_node, atot13907, atot13910]
  decide +kernel

theorem arows13920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13920 = true := by
  rw [show D2M8K2.u13920 = KTree.node D2M8K2.u13916 (nat_lit 30573186) (nat_lit 2170708432) (nat_lit 0) D2M8K2.u13919 from rfl, allE_node, arows13916, irow13920, arows13919]
  all_goals rfl

theorem atot13920 : totK PD2M8K2 D2M8K2.u13920 = [740604073303, 2671710157509, 2884432693774, 896364621022, 50498093060, 0, 0, 0] := by
  rw [show D2M8K2.u13920 = KTree.node D2M8K2.u13916 (nat_lit 30573186) (nat_lit 2170708432) (nat_lit 0) D2M8K2.u13919 from rfl, totK_node, atot13916, atot13919]
  decide +kernel

theorem arows13927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13927 = true := by
  rw [show D2M8K2.u13927 = KTree.node D2M8K2.u13923 (nat_lit 30583122) (nat_lit 3448682590) (nat_lit 0) D2M8K2.u13926 from rfl, allE_node, arows13923, irow13927, arows13926]
  all_goals rfl

theorem atot13927 : totK PD2M8K2 D2M8K2.u13927 = [532815730907, 2494389884916, 3221144476888, 960328316794, 40469446710, 0, 0, 0] := by
  rw [show D2M8K2.u13927 = KTree.node D2M8K2.u13923 (nat_lit 30583122) (nat_lit 3448682590) (nat_lit 0) D2M8K2.u13926 from rfl, totK_node, atot13923, atot13926]
  decide +kernel

theorem arows13935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13935 = true := by
  rw [show D2M8K2.u13935 = KTree.node D2M8K2.u13931 (nat_lit 30590620) (nat_lit 3899941549) (nat_lit 0) D2M8K2.u13934 from rfl, allE_node, arows13931, irow13935, arows13934]
  all_goals rfl

theorem atot13935 : totK PD2M8K2 D2M8K2.u13935 = [0, 942924833609, 3222657889115, 2670734563606, 376466689099, 6190125969, 0, 0] := by
  rw [show D2M8K2.u13935 = KTree.node D2M8K2.u13931 (nat_lit 30590620) (nat_lit 3899941549) (nat_lit 0) D2M8K2.u13934 from rfl, totK_node, atot13931, atot13934]
  decide +kernel

theorem arows13942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13942 = true := by
  rw [show D2M8K2.u13942 = KTree.node D2M8K2.u13938 (nat_lit 30603006) (nat_lit 3853262279) (nat_lit 0) D2M8K2.u13941 from rfl, allE_node, arows13938, irow13942, arows13941]
  all_goals rfl

theorem atot13942 : totK PD2M8K2 D2M8K2.u13942 = [0, 855678557554, 3029246161775, 2751425605307, 524994713383, 13355831902, 0, 0] := by
  rw [show D2M8K2.u13942 = KTree.node D2M8K2.u13938 (nat_lit 30603006) (nat_lit 3853262279) (nat_lit 0) D2M8K2.u13941 from rfl, totK_node, atot13938, atot13941]
  decide +kernel

theorem arows13953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13953 = true := by
  rw [show D2M8K2.u13953 = KTree.node D2M8K2.u13949 (nat_lit 30653983) (nat_lit 2354506643) (nat_lit 0) D2M8K2.u13952 from rfl, allE_node, arows13949, irow13953, arows13952]
  all_goals rfl

theorem atot13953 : totK PD2M8K2 D2M8K2.u13953 = [0, 869549231262, 2822255164062, 2716271196074, 828609873778, 50936138915, 0, 0] := by
  rw [show D2M8K2.u13953 = KTree.node D2M8K2.u13949 (nat_lit 30653983) (nat_lit 2354506643) (nat_lit 0) D2M8K2.u13952 from rfl, totK_node, atot13949, atot13952]
  decide +kernel

theorem arows13960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13960 = true := by
  rw [show D2M8K2.u13960 = KTree.node D2M8K2.u13956 (nat_lit 30660267) (nat_lit 3703598000) (nat_lit 0) D2M8K2.u13959 from rfl, allE_node, arows13956, irow13960, arows13959]
  all_goals rfl

theorem atot13960 : totK PD2M8K2 D2M8K2.u13960 = [0, 822285969658, 2908451608449, 2792498928489, 621203319343, 17530736909, 0, 0] := by
  rw [show D2M8K2.u13960 = KTree.node D2M8K2.u13956 (nat_lit 30660267) (nat_lit 3703598000) (nat_lit 0) D2M8K2.u13959 from rfl, totK_node, atot13956, atot13959]
  decide +kernel

theorem arows13968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13968 = true := by
  rw [show D2M8K2.u13968 = KTree.node D2M8K2.u13964 (nat_lit 30667234) (nat_lit 4167904031) (nat_lit 0) D2M8K2.u13967 from rfl, allE_node, arows13964, irow13968, arows13967]
  all_goals rfl

theorem atot13968 : totK PD2M8K2 D2M8K2.u13968 = [0, 425933657684, 2256454927421, 3288135593174, 1225675969108, 77122613086, 0, 0] := by
  rw [show D2M8K2.u13968 = KTree.node D2M8K2.u13964 (nat_lit 30667234) (nat_lit 4167904031) (nat_lit 0) D2M8K2.u13967 from rfl, totK_node, atot13964, atot13967]
  decide +kernel

theorem arows13975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13975 = true := by
  rw [show D2M8K2.u13975 = KTree.node D2M8K2.u13971 (nat_lit 30676849) (nat_lit 1360866032) (nat_lit 0) D2M8K2.u13974 from rfl, allE_node, arows13971, irow13975, arows13974]
  all_goals rfl

theorem atot13975 : totK PD2M8K2 D2M8K2.u13975 = [0, 0, 796392373185, 2748046451280, 2780878308434, 768274036168, 41989737272, 0] := by
  rw [show D2M8K2.u13975 = KTree.node D2M8K2.u13971 (nat_lit 30676849) (nat_lit 1360866032) (nat_lit 0) D2M8K2.u13974 from rfl, totK_node, atot13971, atot13974]
  decide +kernel

theorem arows13984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13984 = true := by
  rw [show D2M8K2.u13984 = KTree.node D2M8K2.u13980 (nat_lit 30683743) (nat_lit 2388662770) (nat_lit 0) D2M8K2.u13983 from rfl, allE_node, arows13980, irow13984, arows13983]
  all_goals rfl

theorem atot13984 : totK PD2M8K2 D2M8K2.u13984 = [0, 0, 852377554212, 3125553480651, 2750388236278, 415186844948, 6518567072, 0] := by
  rw [show D2M8K2.u13984 = KTree.node D2M8K2.u13980 (nat_lit 30683743) (nat_lit 2388662770) (nat_lit 0) D2M8K2.u13983 from rfl, totK_node, atot13980, atot13983]
  decide +kernel

theorem arows13991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13991 = true := by
  rw [show D2M8K2.u13991 = KTree.node D2M8K2.u13987 (nat_lit 30692457) (nat_lit 1505755647) (nat_lit 0) D2M8K2.u13990 from rfl, allE_node, arows13987, irow13991, arows13990]
  all_goals rfl

theorem atot13991 : totK PD2M8K2 D2M8K2.u13991 = [0, 754346683581, 2509012101332, 2481963249053, 1175855694968, 261992856436, 9139067247, 0] := by
  rw [show D2M8K2.u13991 = KTree.node D2M8K2.u13987 (nat_lit 30692457) (nat_lit 1505755647) (nat_lit 0) D2M8K2.u13990 from rfl, totK_node, atot13987, atot13990]
  decide +kernel

theorem arows13999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13999 = true := by
  rw [show D2M8K2.u13999 = KTree.node D2M8K2.u13995 (nat_lit 30698331) (nat_lit 3684992843) (nat_lit 0) D2M8K2.u13998 from rfl, allE_node, arows13995, irow13999, arows13998]
  all_goals rfl

theorem atot13999 : totK PD2M8K2 D2M8K2.u13999 = [0, 820565466379, 2877440616810, 2798627760847, 668505250808, 23435119741, 0, 0] := by
  rw [show D2M8K2.u13999 = KTree.node D2M8K2.u13995 (nat_lit 30698331) (nat_lit 3684992843) (nat_lit 0) D2M8K2.u13998 from rfl, totK_node, atot13995, atot13998]
  decide +kernel

theorem arows14006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14006 = true := by
  rw [show D2M8K2.u14006 = KTree.node D2M8K2.u14002 (nat_lit 30708963) (nat_lit 2549640539) (nat_lit 0) D2M8K2.u14005 from rfl, allE_node, arows14002, irow14006, arows14005]
  all_goals rfl

theorem atot14006 : totK PD2M8K2 D2M8K2.u14006 = [0, 418584527484, 2280890694316, 3320939655972, 1123013406233, 57842560894, 0, 0] := by
  rw [show D2M8K2.u14006 = KTree.node D2M8K2.u14002 (nat_lit 30708963) (nat_lit 2549640539) (nat_lit 0) D2M8K2.u14005 from rfl, totK_node, atot14002, atot14005]
  decide +kernel

theorem arows14016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14016 = true := by
  rw [show D2M8K2.u14016 = KTree.node D2M8K2.u14012 (nat_lit 30719364) (nat_lit 3064196564) (nat_lit 0) D2M8K2.u14015 from rfl, allE_node, arows14012, irow14016, arows14015]
  all_goals rfl

theorem atot14016 : totK PD2M8K2 D2M8K2.u14016 = [0, 0, 978481561942, 3272983125242, 2493832991861, 333940893054, 5320761635, 0] := by
  rw [show D2M8K2.u14016 = KTree.node D2M8K2.u14012 (nat_lit 30719364) (nat_lit 3064196564) (nat_lit 0) D2M8K2.u14015 from rfl, totK_node, atot14012, atot14015]
  decide +kernel

theorem arows14023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14023 = true := by
  rw [show D2M8K2.u14023 = KTree.node D2M8K2.u14019 (nat_lit 30732481) (nat_lit 1575612183) (nat_lit 0) D2M8K2.u14022 from rfl, allE_node, arows14019, irow14023, arows14022]
  all_goals rfl

theorem atot14023 : totK PD2M8K2 D2M8K2.u14023 = [0, 754535350537, 2763600002530, 2814932520229, 842362347991, 73809014152, 1225787871, 0] := by
  rw [show D2M8K2.u14023 = KTree.node D2M8K2.u14019 (nat_lit 30732481) (nat_lit 1575612183) (nat_lit 0) D2M8K2.u14022 from rfl, totK_node, atot14019, atot14022]
  decide +kernel

theorem arows14031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14031 = true := by
  rw [show D2M8K2.u14031 = KTree.node D2M8K2.u14027 (nat_lit 30742692) (nat_lit 3269005669) (nat_lit 0) D2M8K2.u14030 from rfl, allE_node, arows14027, irow14031, arows14030]
  all_goals rfl

theorem atot14031 : totK PD2M8K2 D2M8K2.u14031 = [0, 801683049388, 2741221046213, 2821353003250, 815412524369, 34821512560, 0, 0] := by
  rw [show D2M8K2.u14031 = KTree.node D2M8K2.u14027 (nat_lit 30742692) (nat_lit 3269005669) (nat_lit 0) D2M8K2.u14030 from rfl, totK_node, atot14027, atot14030]
  decide +kernel

theorem arows14038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14038 = true := by
  rw [show D2M8K2.u14038 = KTree.node D2M8K2.u14034 (nat_lit 30749738) (nat_lit 4070459218) (nat_lit 0) D2M8K2.u14037 from rfl, allE_node, arows14034, irow14038, arows14037]
  all_goals rfl

theorem atot14038 : totK PD2M8K2 D2M8K2.u14038 = [0, 437825367018, 2470471652865, 3299751337918, 964166434264, 47196677274, 0, 0] := by
  rw [show D2M8K2.u14038 = KTree.node D2M8K2.u14034 (nat_lit 30749738) (nat_lit 4070459218) (nat_lit 0) D2M8K2.u14037 from rfl, totK_node, atot14034, atot14037]
  decide +kernel

theorem arows14047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14047 = true := by
  rw [show D2M8K2.u14047 = KTree.node D2M8K2.u14043 (nat_lit 30763564) (nat_lit 3611872793) (nat_lit 0) D2M8K2.u14046 from rfl, allE_node, arows14043, irow14047, arows14046]
  all_goals rfl

theorem atot14047 : totK PD2M8K2 D2M8K2.u14047 = [0, 0, 1089047927912, 3382895691793, 2359764553571, 294538438209, 5352782441, 0] := by
  rw [show D2M8K2.u14047 = KTree.node D2M8K2.u14043 (nat_lit 30763564) (nat_lit 3611872793) (nat_lit 0) D2M8K2.u14046 from rfl, totK_node, atot14043, atot14046]
  decide +kernel

theorem arows14054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14054 = true := by
  rw [show D2M8K2.u14054 = KTree.node D2M8K2.u14050 (nat_lit 30776504) (nat_lit 3865940388) (nat_lit 0) D2M8K2.u14053 from rfl, allE_node, arows14050, irow14054, arows14053]
  all_goals rfl

theorem atot14054 : totK PD2M8K2 D2M8K2.u14054 = [0, 496232549225, 2064496730582, 2957598003895, 1538926366437, 153934789196, 1271866555, 0] := by
  rw [show D2M8K2.u14054 = KTree.node D2M8K2.u14050 (nat_lit 30776504) (nat_lit 3865940388) (nat_lit 0) D2M8K2.u14053 from rfl, totK_node, atot14050, atot14053]
  decide +kernel

theorem arows14062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14062 = true := by
  rw [show D2M8K2.u14062 = KTree.node D2M8K2.u14058 (nat_lit 30782810) (nat_lit 3344282452) (nat_lit 0) D2M8K2.u14061 from rfl, allE_node, arows14058, irow14062, arows14061]
  all_goals rfl

theorem atot14062 : totK PD2M8K2 D2M8K2.u14062 = [0, 808396010853, 2863910768657, 2806423573310, 662569386090, 26300412495, 0, 0] := by
  rw [show D2M8K2.u14062 = KTree.node D2M8K2.u14058 (nat_lit 30782810) (nat_lit 3344282452) (nat_lit 0) D2M8K2.u14061 from rfl, totK_node, atot14058, atot14061]
  decide +kernel

theorem arows14069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14069 = true := by
  rw [show D2M8K2.u14069 = KTree.node D2M8K2.u14065 (nat_lit 30796893) (nat_lit 1406425193) (nat_lit 0) D2M8K2.u14068 from rfl, allE_node, arows14065, irow14069, arows14068]
  all_goals rfl

theorem atot14069 : totK PD2M8K2 D2M8K2.u14069 = [0, 353655970187, 2210642352930, 3357072172092, 1234876078308, 72779307922, 0, 0] := by
  rw [show D2M8K2.u14069 = KTree.node D2M8K2.u14065 (nat_lit 30796893) (nat_lit 1406425193) (nat_lit 0) D2M8K2.u14068 from rfl, totK_node, atot14065, atot14068]
  decide +kernel

theorem arows14081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14081 = true := by
  rw [show D2M8K2.u14081 = KTree.node D2M8K2.u14077 (nat_lit 30807864) (nat_lit 3383441818) (nat_lit 0) D2M8K2.u14080 from rfl, allE_node, arows14077, irow14081, arows14080]
  all_goals rfl

theorem atot14081 : totK PD2M8K2 D2M8K2.u14081 = [0, 342835346343, 1771961520892, 3107254032265, 1743048320742, 194499781303, 1429815836, 0] := by
  rw [show D2M8K2.u14081 = KTree.node D2M8K2.u14077 (nat_lit 30807864) (nat_lit 3383441818) (nat_lit 0) D2M8K2.u14080 from rfl, totK_node, atot14077, atot14080]
  decide +kernel

theorem arows14088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14088 = true := by
  rw [show D2M8K2.u14088 = KTree.node D2M8K2.u14084 (nat_lit 30819487) (nat_lit 1822068176) (nat_lit 0) D2M8K2.u14087 from rfl, allE_node, arows14084, irow14088, arows14087]
  all_goals rfl

theorem atot14088 : totK PD2M8K2 D2M8K2.u14088 = [0, 845733027643, 2867309047820, 2776211639429, 755555123590, 38849856064, 0, 0] := by
  rw [show D2M8K2.u14088 = KTree.node D2M8K2.u14084 (nat_lit 30819487) (nat_lit 1822068176) (nat_lit 0) D2M8K2.u14087 from rfl, totK_node, atot14084, atot14087]
  decide +kernel

theorem arows14096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14096 = true := by
  rw [show D2M8K2.u14096 = KTree.node D2M8K2.u14092 (nat_lit 30825778) (nat_lit 4169091573) (nat_lit 0) D2M8K2.u14095 from rfl, allE_node, arows14092, irow14096, arows14095]
  all_goals rfl

theorem atot14096 : totK PD2M8K2 D2M8K2.u14096 = [0, 858551112672, 2937195682211, 2805266908849, 629742750368, 18248331466, 0, 0] := by
  rw [show D2M8K2.u14096 = KTree.node D2M8K2.u14092 (nat_lit 30825778) (nat_lit 4169091573) (nat_lit 0) D2M8K2.u14095 from rfl, totK_node, atot14092, atot14095]
  decide +kernel

theorem arows14103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14103 = true := by
  rw [show D2M8K2.u14103 = KTree.node D2M8K2.u14099 (nat_lit 30838442) (nat_lit 4124048370) (nat_lit 0) D2M8K2.u14102 from rfl, allE_node, arows14099, irow14103, arows14102]
  all_goals rfl

theorem atot14103 : totK PD2M8K2 D2M8K2.u14103 = [0, 0, 1691706120130, 3774153015277, 1650829013550, 101751227965, 0, 0] := by
  rw [show D2M8K2.u14103 = KTree.node D2M8K2.u14099 (nat_lit 30838442) (nat_lit 4124048370) (nat_lit 0) D2M8K2.u14102 from rfl, totK_node, atot14099, atot14102]
  decide +kernel

theorem arows14112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14112 = true := by
  rw [show D2M8K2.u14112 = KTree.node D2M8K2.u14108 (nat_lit 30847484) (nat_lit 3243853285) (nat_lit 0) D2M8K2.u14111 from rfl, allE_node, arows14108, irow14112, arows14111]
  all_goals rfl

theorem atot14112 : totK PD2M8K2 D2M8K2.u14112 = [0, 0, 842501793838, 3163320993546, 2774570536160, 374446067977, 3885648923, 0] := by
  rw [show D2M8K2.u14112 = KTree.node D2M8K2.u14108 (nat_lit 30847484) (nat_lit 3243853285) (nat_lit 0) D2M8K2.u14111 from rfl, totK_node, atot14108, atot14111]
  decide +kernel

theorem arows14119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14119 = true := by
  rw [show D2M8K2.u14119 = KTree.node D2M8K2.u14115 (nat_lit 30857863) (nat_lit 2383902045) (nat_lit 0) D2M8K2.u14118 from rfl, allE_node, arows14115, irow14119, arows14118]
  all_goals rfl

theorem atot14119 : totK PD2M8K2 D2M8K2.u14119 = [856534553545, 2863653322308, 2390535488721, 522889931974, 383821967815, 163540927763, 8304201444, 0] := by
  rw [show D2M8K2.u14119 = KTree.node D2M8K2.u14115 (nat_lit 30857863) (nat_lit 2383902045) (nat_lit 0) D2M8K2.u14118 from rfl, totK_node, atot14115, atot14118]
  decide +kernel

theorem arows14127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14127 = true := by
  rw [show D2M8K2.u14127 = KTree.node D2M8K2.u14123 (nat_lit 30868824) (nat_lit 3544618027) (nat_lit 0) D2M8K2.u14126 from rfl, allE_node, arows14123, irow14127, arows14126]
  all_goals rfl

theorem atot14127 : totK PD2M8K2 D2M8K2.u14127 = [791156827862, 2839188762808, 2801160044576, 647168690409, 24114632771, 0, 0, 0] := by
  rw [show D2M8K2.u14127 = KTree.node D2M8K2.u14123 (nat_lit 30868824) (nat_lit 3544618027) (nat_lit 0) D2M8K2.u14126 from rfl, totK_node, atot14123, atot14126]
  decide +kernel

theorem arows14134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14134 = true := by
  rw [show D2M8K2.u14134 = KTree.node D2M8K2.u14130 (nat_lit 30875904) (nat_lit 3766812078) (nat_lit 0) D2M8K2.u14133 from rfl, allE_node, arows14130, irow14134, arows14133]
  all_goals rfl

theorem atot14134 : totK PD2M8K2 D2M8K2.u14134 = [328860779294, 1816406306318, 3138833394413, 1627423830904, 186534312951, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14134 = KTree.node D2M8K2.u14130 (nat_lit 30875904) (nat_lit 3766812078) (nat_lit 0) D2M8K2.u14133 from rfl, totK_node, atot14130, atot14133]
  decide +kernel

theorem arows14144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14144 = true := by
  rw [show D2M8K2.u14144 = KTree.node D2M8K2.u14140 (nat_lit 30889858) (nat_lit 3896605312) (nat_lit 0) D2M8K2.u14143 from rfl, allE_node, arows14140, irow14144, arows14143]
  all_goals rfl

theorem atot14144 : totK PD2M8K2 D2M8K2.u14144 = [0, 1452665136099, 3769535744745, 1820600747749, 95167823809, 0, 0, 0] := by
  rw [show D2M8K2.u14144 = KTree.node D2M8K2.u14140 (nat_lit 30889858) (nat_lit 3896605312) (nat_lit 0) D2M8K2.u14143 from rfl, totK_node, atot14140, atot14143]
  decide +kernel

theorem arows14151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14151 = true := by
  rw [show D2M8K2.u14151 = KTree.node D2M8K2.u14147 (nat_lit 30902985) (nat_lit 1834682607) (nat_lit 0) D2M8K2.u14150 from rfl, allE_node, arows14147, irow14151, arows14150]
  all_goals rfl

theorem atot14151 : totK PD2M8K2 D2M8K2.u14151 = [867496502247, 2875065560036, 2736514906938, 778669497513, 45866246325, 0, 0, 0] := by
  rw [show D2M8K2.u14151 = KTree.node D2M8K2.u14147 (nat_lit 30902985) (nat_lit 1834682607) (nat_lit 0) D2M8K2.u14150 from rfl, totK_node, atot14147, atot14150]
  decide +kernel

theorem arows14159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14159 = true := by
  rw [show D2M8K2.u14159 = KTree.node D2M8K2.u14155 (nat_lit 30910140) (nat_lit 2355117100) (nat_lit 0) D2M8K2.u14158 from rfl, allE_node, arows14155, irow14159, arows14158]
  all_goals rfl

theorem atot14159 : totK PD2M8K2 D2M8K2.u14159 = [764045423139, 2839509150710, 2935366237552, 688615806244, 27693597685, 0, 0, 0] := by
  rw [show D2M8K2.u14159 = KTree.node D2M8K2.u14155 (nat_lit 30910140) (nat_lit 2355117100) (nat_lit 0) D2M8K2.u14158 from rfl, totK_node, atot14155, atot14158]
  decide +kernel

theorem arows14166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14166 = true := by
  rw [show D2M8K2.u14166 = KTree.node D2M8K2.u14162 (nat_lit 30917254) (nat_lit 3475580784) (nat_lit 0) D2M8K2.u14165 from rfl, allE_node, arows14162, irow14166, arows14165]
  all_goals rfl

theorem atot14166 : totK PD2M8K2 D2M8K2.u14166 = [369552348654, 1865063884147, 2956755933821, 1702575834923, 382707379484, 26904681413, 0, 0] := by
  rw [show D2M8K2.u14166 = KTree.node D2M8K2.u14162 (nat_lit 30917254) (nat_lit 3475580784) (nat_lit 0) D2M8K2.u14165 from rfl, totK_node, atot14162, atot14165]
  decide +kernel

theorem arows14175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14175 = true := by
  rw [show D2M8K2.u14175 = KTree.node D2M8K2.u14171 (nat_lit 30926712) (nat_lit 3234738714) (nat_lit 0) D2M8K2.u14174 from rfl, allE_node, arows14171, irow14175, arows14174]
  all_goals rfl

theorem atot14175 : totK PD2M8K2 D2M8K2.u14175 = [0, 754234813966, 2828996104675, 2933330293047, 691290164008, 19347877532, 0, 0] := by
  rw [show D2M8K2.u14175 = KTree.node D2M8K2.u14171 (nat_lit 30926712) (nat_lit 3234738714) (nat_lit 0) D2M8K2.u14174 from rfl, totK_node, atot14171, atot14174]
  decide +kernel

theorem arows14182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14182 = true := by
  rw [show D2M8K2.u14182 = KTree.node D2M8K2.u14178 (nat_lit 30935034) (nat_lit 3904249591) (nat_lit 0) D2M8K2.u14181 from rfl, allE_node, arows14178, irow14182, arows14181]
  all_goals rfl

theorem atot14182 : totK PD2M8K2 D2M8K2.u14182 = [108461727635, 1043127099927, 2941727750575, 2640497015993, 505710585717, 10717512769, 0, 0] := by
  rw [show D2M8K2.u14182 = KTree.node D2M8K2.u14178 (nat_lit 30935034) (nat_lit 3904249591) (nat_lit 0) D2M8K2.u14181 from rfl, totK_node, atot14178, atot14181]
  decide +kernel

theorem arows14190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14190 = true := by
  rw [show D2M8K2.u14190 = KTree.node D2M8K2.u14186 (nat_lit 30942267) (nat_lit 3642318905) (nat_lit 0) D2M8K2.u14189 from rfl, allE_node, arows14186, irow14190, arows14189]
  all_goals rfl

theorem atot14190 : totK PD2M8K2 D2M8K2.u14190 = [765435321426, 2781812046314, 2843350848906, 772512417728, 38760994994, 0, 0, 0] := by
  rw [show D2M8K2.u14190 = KTree.node D2M8K2.u14186 (nat_lit 30942267) (nat_lit 3642318905) (nat_lit 0) D2M8K2.u14189 from rfl, totK_node, atot14186, atot14189]
  decide +kernel

theorem arows14197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14197 = true := by
  rw [show D2M8K2.u14197 = KTree.node D2M8K2.u14193 (nat_lit 30948219) (nat_lit 3742177130) (nat_lit 0) D2M8K2.u14196 from rfl, allE_node, arows14193, irow14197, arows14196]
  all_goals rfl

theorem atot14197 : totK PD2M8K2 D2M8K2.u14197 = [816138955185, 2954415902459, 2839164380259, 576727558236, 18030242193, 0, 0, 0] := by
  rw [show D2M8K2.u14197 = KTree.node D2M8K2.u14193 (nat_lit 30948219) (nat_lit 3742177130) (nat_lit 0) D2M8K2.u14196 from rfl, totK_node, atot14193, atot14196]
  decide +kernel

theorem arows14208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14208 = true := by
  rw [show D2M8K2.u14208 = KTree.node D2M8K2.u14204 (nat_lit 30958621) (nat_lit 1168957538) (nat_lit 0) D2M8K2.u14207 from rfl, allE_node, arows14204, irow14208, arows14207]
  all_goals rfl

theorem atot14208 : totK PD2M8K2 D2M8K2.u14208 = [413128340692, 1960658360069, 3076093485161, 1533756633056, 142210042150, 1206465782, 0, 0] := by
  rw [show D2M8K2.u14208 = KTree.node D2M8K2.u14204 (nat_lit 30958621) (nat_lit 1168957538) (nat_lit 0) D2M8K2.u14207 from rfl, totK_node, atot14204, atot14207]
  decide +kernel

theorem arows14215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14215 = true := by
  rw [show D2M8K2.u14215 = KTree.node D2M8K2.u14211 (nat_lit 30967089) (nat_lit 1601942838) (nat_lit 0) D2M8K2.u14214 from rfl, allE_node, arows14211, irow14215, arows14214]
  all_goals rfl

theorem atot14215 : totK PD2M8K2 D2M8K2.u14215 = [0, 1132776067342, 3334179709905, 2310395608999, 375347742830, 13016197374, 0, 0] := by
  rw [show D2M8K2.u14215 = KTree.node D2M8K2.u14211 (nat_lit 30967089) (nat_lit 1601942838) (nat_lit 0) D2M8K2.u14214 from rfl, totK_node, atot14211, atot14214]
  decide +kernel

theorem arows14223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14223 = true := by
  rw [show D2M8K2.u14223 = KTree.node D2M8K2.u14219 (nat_lit 30977651) (nat_lit 2907377834) (nat_lit 0) D2M8K2.u14222 from rfl, allE_node, arows14219, irow14223, arows14222]
  all_goals rfl

theorem atot14223 : totK PD2M8K2 D2M8K2.u14223 = [433803088254, 1966747024085, 2931707537775, 1547361553540, 201778897575, 4574395652, 0, 0] := by
  rw [show D2M8K2.u14223 = KTree.node D2M8K2.u14219 (nat_lit 30977651) (nat_lit 2907377834) (nat_lit 0) D2M8K2.u14222 from rfl, totK_node, atot14219, atot14222]
  decide +kernel

theorem arows14230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14230 = true := by
  rw [show D2M8K2.u14230 = KTree.node D2M8K2.u14226 (nat_lit 31027653) (nat_lit 1409560813) (nat_lit 0) D2M8K2.u14229 from rfl, allE_node, arows14226, irow14230, arows14229]
  all_goals rfl

theorem atot14230 : totK PD2M8K2 D2M8K2.u14230 = [793409707249, 2782337242242, 2799323873962, 838664943610, 47155980079, 0, 0, 0] := by
  rw [show D2M8K2.u14230 = KTree.node D2M8K2.u14226 (nat_lit 31027653) (nat_lit 1409560813) (nat_lit 0) D2M8K2.u14229 from rfl, totK_node, atot14226, atot14229]
  decide +kernel

theorem arows14239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14239 = true := by
  rw [show D2M8K2.u14239 = KTree.node D2M8K2.u14235 (nat_lit 31037566) (nat_lit 3096868982) (nat_lit 0) D2M8K2.u14238 from rfl, allE_node, arows14235, irow14239, arows14238]
  all_goals rfl

theorem atot14239 : totK PD2M8K2 D2M8K2.u14239 = [424157580399, 2078426821681, 3129514576309, 1345956385155, 119550379393, 1138244013, 0, 0] := by
  rw [show D2M8K2.u14239 = KTree.node D2M8K2.u14235 (nat_lit 31037566) (nat_lit 3096868982) (nat_lit 0) D2M8K2.u14238 from rfl, totK_node, atot14235, atot14238]
  decide +kernel

theorem arows14246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14246 = true := by
  rw [show D2M8K2.u14246 = KTree.node D2M8K2.u14242 (nat_lit 31050172) (nat_lit 3901800563) (nat_lit 0) D2M8K2.u14245 from rfl, allE_node, arows14242, irow14246, arows14245]
  all_goals rfl

theorem atot14246 : totK PD2M8K2 D2M8K2.u14246 = [0, 1188726184343, 3515860142949, 2219097126587, 227767053242, 1095107716, 0, 0] := by
  rw [show D2M8K2.u14246 = KTree.node D2M8K2.u14242 (nat_lit 31050172) (nat_lit 3901800563) (nat_lit 0) D2M8K2.u14245 from rfl, totK_node, atot14242, atot14245]
  decide +kernel

theorem arows14254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14254 = true := by
  rw [show D2M8K2.u14254 = KTree.node D2M8K2.u14250 (nat_lit 31066357) (nat_lit 918277859) (nat_lit 0) D2M8K2.u14253 from rfl, allE_node, arows14250, irow14254, arows14253]
  all_goals rfl

theorem atot14254 : totK PD2M8K2 D2M8K2.u14254 = [827829092807, 2869194617059, 2691423612660, 744622597384, 102298827016, 3882006667, 0, 0] := by
  rw [show D2M8K2.u14254 = KTree.node D2M8K2.u14250 (nat_lit 31066357) (nat_lit 918277859) (nat_lit 0) D2M8K2.u14253 from rfl, totK_node, atot14250, atot14253]
  decide +kernel

theorem arows14261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14261 = true := by
  rw [show D2M8K2.u14261 = KTree.node D2M8K2.u14257 (nat_lit 31072325) (nat_lit 2299794389) (nat_lit 0) D2M8K2.u14260 from rfl, allE_node, arows14257, irow14261, arows14260]
  all_goals rfl

theorem atot14261 : totK PD2M8K2 D2M8K2.u14261 = [790399256756, 2837695148090, 2902265585545, 715718676540, 29397895755, 0, 0, 0] := by
  rw [show D2M8K2.u14261 = KTree.node D2M8K2.u14257 (nat_lit 31072325) (nat_lit 2299794389) (nat_lit 0) D2M8K2.u14260 from rfl, totK_node, atot14257, atot14260]
  decide +kernel

theorem arows14271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14271 = true := by
  rw [show D2M8K2.u14271 = KTree.node D2M8K2.u14267 (nat_lit 31082983) (nat_lit 2211002723) (nat_lit 0) D2M8K2.u14270 from rfl, allE_node, arows14267, irow14271, arows14270]
  all_goals rfl

theorem atot14271 : totK PD2M8K2 D2M8K2.u14271 = [424455604040, 1969778026474, 3062093174130, 1586693917134, 147369503590, 1310285577, 0, 0] := by
  rw [show D2M8K2.u14271 = KTree.node D2M8K2.u14267 (nat_lit 31082983) (nat_lit 2211002723) (nat_lit 0) D2M8K2.u14270 from rfl, totK_node, atot14267, atot14270]
  decide +kernel

theorem arows14278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14278 = true := by
  rw [show D2M8K2.u14278 = KTree.node D2M8K2.u14274 (nat_lit 31091397) (nat_lit 1513106895) (nat_lit 0) D2M8K2.u14277 from rfl, allE_node, arows14274, irow14278, arows14277]
  all_goals rfl

theorem atot14278 : totK PD2M8K2 D2M8K2.u14278 = [0, 1187140821148, 3419770950778, 2344910503695, 300578878813, 4879840392, 0, 0] := by
  rw [show D2M8K2.u14278 = KTree.node D2M8K2.u14274 (nat_lit 31091397) (nat_lit 1513106895) (nat_lit 0) D2M8K2.u14277 from rfl, totK_node, atot14274, atot14277]
  decide +kernel

theorem arows14286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14286 = true := by
  rw [show D2M8K2.u14286 = KTree.node D2M8K2.u14282 (nat_lit 31102356) (nat_lit 3146175521) (nat_lit 0) D2M8K2.u14285 from rfl, allE_node, arows14282, irow14286, arows14285]
  all_goals rfl

theorem atot14286 : totK PD2M8K2 D2M8K2.u14286 = [0, 874339869792, 2939439491939, 2697507523638, 613614936470, 26682572712, 0, 0] := by
  rw [show D2M8K2.u14286 = KTree.node D2M8K2.u14282 (nat_lit 31102356) (nat_lit 3146175521) (nat_lit 0) D2M8K2.u14285 from rfl, totK_node, atot14282, atot14285]
  decide +kernel

theorem arows14293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14293 = true := by
  rw [show D2M8K2.u14293 = KTree.node D2M8K2.u14289 (nat_lit 31112619) (nat_lit 3421225886) (nat_lit 0) D2M8K2.u14292 from rfl, allE_node, arows14289, irow14293, arows14292]
  all_goals rfl

theorem atot14293 : totK PD2M8K2 D2M8K2.u14293 = [0, 747212298849, 2938026324098, 2899060918141, 551584883181, 15616951058, 0, 0] := by
  rw [show D2M8K2.u14293 = KTree.node D2M8K2.u14289 (nat_lit 31112619) (nat_lit 3421225886) (nat_lit 0) D2M8K2.u14292 from rfl, totK_node, atot14289, atot14292]
  decide +kernel

theorem arows14302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14302 = true := by
  rw [show D2M8K2.u14302 = KTree.node D2M8K2.u14298 (nat_lit 31120782) (nat_lit 3996905296) (nat_lit 0) D2M8K2.u14301 from rfl, allE_node, arows14298, irow14302, arows14301]
  all_goals rfl

theorem atot14302 : totK PD2M8K2 D2M8K2.u14302 = [0, 793484814992, 2991459968787, 2872637933490, 501496624698, 9885265364, 0, 0] := by
  rw [show D2M8K2.u14302 = KTree.node D2M8K2.u14298 (nat_lit 31120782) (nat_lit 3996905296) (nat_lit 0) D2M8K2.u14301 from rfl, totK_node, atot14298, atot14301]
  decide +kernel

theorem arows14309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14309 = true := by
  rw [show D2M8K2.u14309 = KTree.node D2M8K2.u14305 (nat_lit 31131721) (nat_lit 1515937386) (nat_lit 0) D2M8K2.u14308 from rfl, allE_node, arows14305, irow14309, arows14308]
  all_goals rfl

theorem atot14309 : totK PD2M8K2 D2M8K2.u14309 = [0, 0, 1361696425039, 3629478240502, 1820526726189, 155099896499, 1275377855, 0] := by
  rw [show D2M8K2.u14309 = KTree.node D2M8K2.u14305 (nat_lit 31131721) (nat_lit 1515937386) (nat_lit 0) D2M8K2.u14308 from rfl, totK_node, atot14305, atot14308]
  decide +kernel

theorem arows14317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14317 = true := by
  rw [show D2M8K2.u14317 = KTree.node D2M8K2.u14313 (nat_lit 31149640) (nat_lit 3844769005) (nat_lit 0) D2M8K2.u14316 from rfl, allE_node, arows14313, irow14317, arows14316]
  all_goals rfl

theorem atot14317 : totK PD2M8K2 D2M8K2.u14317 = [0, 442320105017, 2226129218218, 3274899939600, 1203166544307, 64040734537, 0, 0] := by
  rw [show D2M8K2.u14317 = KTree.node D2M8K2.u14313 (nat_lit 31149640) (nat_lit 3844769005) (nat_lit 0) D2M8K2.u14316 from rfl, totK_node, atot14313, atot14316]
  decide +kernel

theorem arows14324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14324 = true := by
  rw [show D2M8K2.u14324 = KTree.node D2M8K2.u14320 (nat_lit 31155684) (nat_lit 3198248759) (nat_lit 0) D2M8K2.u14323 from rfl, allE_node, arows14320, irow14324, arows14323]
  all_goals rfl

theorem atot14324 : totK PD2M8K2 D2M8K2.u14324 = [0, 896685803592, 3054883627481, 2772326052508, 547965235983, 19486639065, 0, 0] := by
  rw [show D2M8K2.u14324 = KTree.node D2M8K2.u14320 (nat_lit 31155684) (nat_lit 3198248759) (nat_lit 0) D2M8K2.u14323 from rfl, totK_node, atot14320, atot14323]
  decide +kernel

theorem arows14339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14339 = true := by
  rw [show D2M8K2.u14339 = KTree.node D2M8K2.u14335 (nat_lit 31163593) (nat_lit 1418716912) (nat_lit 0) D2M8K2.u14338 from rfl, allE_node, arows14335, irow14339, arows14338]
  all_goals rfl

theorem atot14339 : totK PD2M8K2 D2M8K2.u14339 = [0, 876242438490, 2998097821254, 2753842059139, 604550116182, 21671986373, 0, 0] := by
  rw [show D2M8K2.u14339 = KTree.node D2M8K2.u14335 (nat_lit 31163593) (nat_lit 1418716912) (nat_lit 0) D2M8K2.u14338 from rfl, totK_node, atot14335, atot14338]
  decide +kernel

theorem arows14346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14346 = true := by
  rw [show D2M8K2.u14346 = KTree.node D2M8K2.u14342 (nat_lit 31191530) (nat_lit 4023974428) (nat_lit 0) D2M8K2.u14345 from rfl, allE_node, arows14342, irow14346, arows14345]
  all_goals rfl

theorem atot14346 : totK PD2M8K2 D2M8K2.u14346 = [0, 795042137247, 2907087482133, 2840906403641, 641296741139, 25423285626, 0, 0] := by
  rw [show D2M8K2.u14346 = KTree.node D2M8K2.u14342 (nat_lit 31191530) (nat_lit 4023974428) (nat_lit 0) D2M8K2.u14345 from rfl, totK_node, atot14342, atot14345]
  decide +kernel

theorem arows14354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14354 = true := by
  rw [show D2M8K2.u14354 = KTree.node D2M8K2.u14350 (nat_lit 31201161) (nat_lit 1905615121) (nat_lit 0) D2M8K2.u14353 from rfl, allE_node, arows14350, irow14354, arows14353]
  all_goals rfl

theorem atot14354 : totK PD2M8K2 D2M8K2.u14354 = [0, 840877774013, 2965805847370, 2792988434020, 550805858908, 17896035637, 0, 0] := by
  rw [show D2M8K2.u14354 = KTree.node D2M8K2.u14350 (nat_lit 31201161) (nat_lit 1905615121) (nat_lit 0) D2M8K2.u14353 from rfl, totK_node, atot14350, atot14353]
  decide +kernel

theorem arows14361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14361 = true := by
  rw [show D2M8K2.u14361 = KTree.node D2M8K2.u14357 (nat_lit 31208389) (nat_lit 1350695207) (nat_lit 0) D2M8K2.u14360 from rfl, allE_node, arows14357, irow14361, arows14360]
  all_goals rfl

theorem atot14361 : totK PD2M8K2 D2M8K2.u14361 = [0, 250501968678, 1765885809638, 3292107421163, 1604425419480, 153459184825, 1206465782, 0] := by
  rw [show D2M8K2.u14361 = KTree.node D2M8K2.u14357 (nat_lit 31208389) (nat_lit 1350695207) (nat_lit 0) D2M8K2.u14360 from rfl, totK_node, atot14357, atot14360]
  decide +kernel

theorem arows14370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14370 = true := by
  rw [show D2M8K2.u14370 = KTree.node D2M8K2.u14366 (nat_lit 31216996) (nat_lit 3881538657) (nat_lit 0) D2M8K2.u14369 from rfl, allE_node, arows14366, irow14370, arows14369]
  all_goals rfl

theorem atot14370 : totK PD2M8K2 D2M8K2.u14370 = [0, 0, 973094530960, 3186399573867, 2394670129258, 415302374154, 14037798012, 0] := by
  rw [show D2M8K2.u14370 = KTree.node D2M8K2.u14366 (nat_lit 31216996) (nat_lit 3881538657) (nat_lit 0) D2M8K2.u14369 from rfl, totK_node, atot14366, atot14369]
  decide +kernel

theorem arows14377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14377 = true := by
  rw [show D2M8K2.u14377 = KTree.node D2M8K2.u14373 (nat_lit 31271088) (nat_lit 3539834764) (nat_lit 0) D2M8K2.u14376 from rfl, allE_node, arows14373, irow14377, arows14376]
  all_goals rfl

theorem atot14377 : totK PD2M8K2 D2M8K2.u14377 = [0, 749943018193, 2691773189677, 2729089001269, 842243251672, 101427148564, 3552795014, 0] := by
  rw [show D2M8K2.u14377 = KTree.node D2M8K2.u14373 (nat_lit 31271088) (nat_lit 3539834764) (nat_lit 0) D2M8K2.u14376 from rfl, totK_node, atot14373, atot14376]
  decide +kernel

theorem arows14385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14385 = true := by
  rw [show D2M8K2.u14385 = KTree.node D2M8K2.u14381 (nat_lit 31278147) (nat_lit 2563509842) (nat_lit 0) D2M8K2.u14384 from rfl, allE_node, arows14381, irow14385, arows14384]
  all_goals rfl

theorem atot14385 : totK PD2M8K2 D2M8K2.u14385 = [0, 805744674932, 2846402884804, 2843782222840, 711993312331, 28063716506, 0, 0] := by
  rw [show D2M8K2.u14385 = KTree.node D2M8K2.u14381 (nat_lit 31278147) (nat_lit 2563509842) (nat_lit 0) D2M8K2.u14384 from rfl, totK_node, atot14381, atot14384]
  decide +kernel

theorem arows14392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14392 = true := by
  rw [show D2M8K2.u14392 = KTree.node D2M8K2.u14388 (nat_lit 31292080) (nat_lit 3275329215) (nat_lit 0) D2M8K2.u14391 from rfl, allE_node, arows14388, irow14392, arows14391]
  all_goals rfl

theorem atot14392 : totK PD2M8K2 D2M8K2.u14392 = [0, 92237621127, 1682089231260, 3579091894460, 1563796597266, 115461420718, 1103454931, 0] := by
  rw [show D2M8K2.u14392 = KTree.node D2M8K2.u14388 (nat_lit 31292080) (nat_lit 3275329215) (nat_lit 0) D2M8K2.u14391 from rfl, totK_node, atot14388, atot14391]
  decide +kernel

theorem arows14402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14402 = true := by
  rw [show D2M8K2.u14402 = KTree.node D2M8K2.u14398 (nat_lit 31306417) (nat_lit 1423666189) (nat_lit 0) D2M8K2.u14401 from rfl, allE_node, arows14398, irow14402, arows14401]
  all_goals rfl

theorem atot14402 : totK PD2M8K2 D2M8K2.u14402 = [0, 407385632425, 1877786790385, 2967283896449, 1549581080646, 192389526020, 4779662215, 0] := by
  rw [show D2M8K2.u14402 = KTree.node D2M8K2.u14398 (nat_lit 31306417) (nat_lit 1423666189) (nat_lit 0) D2M8K2.u14401 from rfl, totK_node, atot14398, atot14401]
  decide +kernel

theorem arows14409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14409 = true := by
  rw [show D2M8K2.u14409 = KTree.node D2M8K2.u14405 (nat_lit 31317378) (nat_lit 875619536) (nat_lit 0) D2M8K2.u14408 from rfl, allE_node, arows14405, irow14409, arows14408]
  all_goals rfl

theorem atot14409 : totK PD2M8K2 D2M8K2.u14409 = [0, 844270211871, 2895529207459, 2792721687703, 702780203774, 33926718517, 0, 0] := by
  rw [show D2M8K2.u14409 = KTree.node D2M8K2.u14405 (nat_lit 31317378) (nat_lit 875619536) (nat_lit 0) D2M8K2.u14408 from rfl, totK_node, atot14405, atot14408]
  decide +kernel

theorem arows14417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14417 = true := by
  rw [show D2M8K2.u14417 = KTree.node D2M8K2.u14413 (nat_lit 31324419) (nat_lit 2655414779) (nat_lit 0) D2M8K2.u14416 from rfl, allE_node, arows14413, irow14417, arows14416]
  all_goals rfl

theorem atot14417 : totK PD2M8K2 D2M8K2.u14417 = [0, 787232016405, 2962680295026, 2940095887982, 597960270213, 15952459745, 0, 0] := by
  rw [show D2M8K2.u14417 = KTree.node D2M8K2.u14413 (nat_lit 31324419) (nat_lit 2655414779) (nat_lit 0) D2M8K2.u14416 from rfl, totK_node, atot14413, atot14416]
  decide +kernel

theorem arows14424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14424 = true := by
  rw [show D2M8K2.u14424 = KTree.node D2M8K2.u14420 (nat_lit 31355201) (nat_lit 2222159759) (nat_lit 0) D2M8K2.u14423 from rfl, allE_node, arows14420, irow14424, arows14423]
  all_goals rfl

theorem atot14424 : totK PD2M8K2 D2M8K2.u14424 = [758382914429, 2630192947001, 2518857275021, 941382533338, 270283332562, 19678284834, 0, 0] := by
  rw [show D2M8K2.u14424 = KTree.node D2M8K2.u14420 (nat_lit 31355201) (nat_lit 2222159759) (nat_lit 0) D2M8K2.u14423 from rfl, totK_node, atot14420, atot14423]
  decide +kernel

theorem arows14433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14433 = true := by
  rw [show D2M8K2.u14433 = KTree.node D2M8K2.u14429 (nat_lit 31366281) (nat_lit 1616867665) (nat_lit 0) D2M8K2.u14432 from rfl, allE_node, arows14429, irow14433, arows14432]
  all_goals rfl

theorem atot14433 : totK PD2M8K2 D2M8K2.u14433 = [831241321846, 2924619443652, 2788917330818, 591226030977, 18231200220, 0, 0, 0] := by
  rw [show D2M8K2.u14433 = KTree.node D2M8K2.u14429 (nat_lit 31366281) (nat_lit 1616867665) (nat_lit 0) D2M8K2.u14432 from rfl, totK_node, atot14429, atot14432]
  decide +kernel

theorem arows14440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14440 = true := by
  rw [show D2M8K2.u14440 = KTree.node D2M8K2.u14436 (nat_lit 31373401) (nat_lit 1500477366) (nat_lit 0) D2M8K2.u14439 from rfl, allE_node, arows14436, irow14440, arows14439]
  all_goals rfl

theorem atot14440 : totK PD2M8K2 D2M8K2.u14440 = [387121083410, 1879969201901, 3060151247987, 1588309444010, 179580293232, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14440 = KTree.node D2M8K2.u14436 (nat_lit 31373401) (nat_lit 1500477366) (nat_lit 0) D2M8K2.u14439 from rfl, totK_node, atot14436, atot14439]
  decide +kernel

theorem arows14448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14448 = true := by
  rw [show D2M8K2.u14448 = KTree.node D2M8K2.u14444 (nat_lit 31385611) (nat_lit 1585534026) (nat_lit 0) D2M8K2.u14447 from rfl, allE_node, arows14444, irow14448, arows14447]
  all_goals rfl

theorem atot14448 : totK PD2M8K2 D2M8K2.u14448 = [0, 1505597497091, 3778029562949, 1767066933974, 95795968684, 0, 0, 0] := by
  rw [show D2M8K2.u14448 = KTree.node D2M8K2.u14444 (nat_lit 31385611) (nat_lit 1585534026) (nat_lit 0) D2M8K2.u14447 from rfl, totK_node, atot14444, atot14447]
  decide +kernel

theorem arows14455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14455 = true := by
  rw [show D2M8K2.u14455 = KTree.node D2M8K2.u14451 (nat_lit 31400454) (nat_lit 3872665113) (nat_lit 0) D2M8K2.u14454 from rfl, allE_node, arows14451, irow14455, arows14454]
  all_goals rfl

theorem atot14455 : totK PD2M8K2 D2M8K2.u14455 = [774308869471, 2713738850335, 2859654647971, 922310792432, 59376079511, 0, 0, 0] := by
  rw [show D2M8K2.u14455 = KTree.node D2M8K2.u14451 (nat_lit 31400454) (nat_lit 3872665113) (nat_lit 0) D2M8K2.u14454 from rfl, totK_node, atot14451, atot14454]
  decide +kernel

theorem arows14466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14466 = true := by
  rw [show D2M8K2.u14466 = KTree.node D2M8K2.u14462 (nat_lit 31407608) (nat_lit 3771108035) (nat_lit 0) D2M8K2.u14465 from rfl, allE_node, arows14462, irow14466, arows14465]
  all_goals rfl

theorem atot14466 : totK PD2M8K2 D2M8K2.u14466 = [807721595797, 2962898503454, 2871924877207, 580669280928, 16744629650, 0, 0, 0] := by
  rw [show D2M8K2.u14466 = KTree.node D2M8K2.u14462 (nat_lit 31407608) (nat_lit 3771108035) (nat_lit 0) D2M8K2.u14465 from rfl, totK_node, atot14462, atot14465]
  decide +kernel

theorem arows14473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14473 = true := by
  rw [show D2M8K2.u14473 = KTree.node D2M8K2.u14469 (nat_lit 31414763) (nat_lit 2940743118) (nat_lit 0) D2M8K2.u14472 from rfl, allE_node, arows14469, irow14473, arows14472]
  all_goals rfl

theorem atot14473 : totK PD2M8K2 D2M8K2.u14473 = [419286654820, 1939484138372, 2976101087327, 1603596339869, 327833149151, 25191558099, 0, 0] := by
  rw [show D2M8K2.u14473 = KTree.node D2M8K2.u14469 (nat_lit 31414763) (nat_lit 2940743118) (nat_lit 0) D2M8K2.u14472 from rfl, totK_node, atot14469, atot14472]
  decide +kernel

theorem arows14481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14481 = true := by
  rw [show D2M8K2.u14481 = KTree.node D2M8K2.u14477 (nat_lit 31424918) (nat_lit 3703645189) (nat_lit 0) D2M8K2.u14480 from rfl, allE_node, arows14477, irow14481, arows14480]
  all_goals rfl

theorem atot14481 : totK PD2M8K2 D2M8K2.u14481 = [0, 754310540250, 2822635559266, 2940677091073, 701003586643, 20922116152, 0, 0] := by
  rw [show D2M8K2.u14481 = KTree.node D2M8K2.u14477 (nat_lit 31424918) (nat_lit 3703645189) (nat_lit 0) D2M8K2.u14480 from rfl, totK_node, atot14477, atot14480]
  decide +kernel

theorem arows14488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14488 = true := by
  rw [show D2M8K2.u14488 = KTree.node D2M8K2.u14484 (nat_lit 31432471) (nat_lit 1796271711) (nat_lit 0) D2M8K2.u14487 from rfl, allE_node, arows14484, irow14488, arows14487]
  all_goals rfl

theorem atot14488 : totK PD2M8K2 D2M8K2.u14488 = [71933061318, 899455269037, 2935568927796, 2772664584050, 552493025829, 11904453692, 0, 0] := by
  rw [show D2M8K2.u14488 = KTree.node D2M8K2.u14484 (nat_lit 31432471) (nat_lit 1796271711) (nat_lit 0) D2M8K2.u14487 from rfl, totK_node, atot14484, atot14487]
  decide +kernel

theorem arows14497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14497 = true := by
  rw [show D2M8K2.u14497 = KTree.node D2M8K2.u14493 (nat_lit 31481253) (nat_lit 1404666214) (nat_lit 0) D2M8K2.u14496 from rfl, allE_node, arows14493, irow14497, arows14496]
  all_goals rfl

theorem atot14497 : totK PD2M8K2 D2M8K2.u14497 = [764941408734, 2873863581892, 2850763232229, 687230640332, 31982243625, 0, 0, 0] := by
  rw [show D2M8K2.u14497 = KTree.node D2M8K2.u14493 (nat_lit 31481253) (nat_lit 1404666214) (nat_lit 0) D2M8K2.u14496 from rfl, totK_node, atot14493, atot14496]
  decide +kernel

theorem arows14504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14504 = true := by
  rw [show D2M8K2.u14504 = KTree.node D2M8K2.u14500 (nat_lit 31490589) (nat_lit 1568520803) (nat_lit 0) D2M8K2.u14503 from rfl, allE_node, arows14500, irow14504, arows14503]
  all_goals rfl

theorem atot14504 : totK PD2M8K2 D2M8K2.u14504 = [846007803221, 2978268340644, 2783583187087, 593268447831, 21122950556, 0, 0, 0] := by
  rw [show D2M8K2.u14504 = KTree.node D2M8K2.u14500 (nat_lit 31490589) (nat_lit 1568520803) (nat_lit 0) D2M8K2.u14503 from rfl, totK_node, atot14500, atot14503]
  decide +kernel

theorem arows14512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14512 = true := by
  rw [show D2M8K2.u14512 = KTree.node D2M8K2.u14508 (nat_lit 31497277) (nat_lit 1065103901) (nat_lit 0) D2M8K2.u14511 from rfl, allE_node, arows14508, irow14512, arows14511]
  all_goals rfl

theorem atot14512 : totK PD2M8K2 D2M8K2.u14512 = [424393285092, 1950346165390, 3079682533230, 1522416214094, 139964657093, 1239866073, 0, 0] := by
  rw [show D2M8K2.u14512 = KTree.node D2M8K2.u14508 (nat_lit 31497277) (nat_lit 1065103901) (nat_lit 0) D2M8K2.u14511 from rfl, totK_node, atot14508, atot14511]
  decide +kernel

theorem arows14519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14519 = true := by
  rw [show D2M8K2.u14519 = KTree.node D2M8K2.u14515 (nat_lit 31509487) (nat_lit 2353934900) (nat_lit 0) D2M8K2.u14518 from rfl, allE_node, arows14515, irow14519, arows14518]
  all_goals rfl

theorem atot14519 : totK PD2M8K2 D2M8K2.u14519 = [0, 1091701505371, 3280564292290, 2397326049961, 389839632714, 13105450397, 0, 0] := by
  rw [show D2M8K2.u14519 = KTree.node D2M8K2.u14515 (nat_lit 31509487) (nat_lit 2353934900) (nat_lit 0) D2M8K2.u14518 from rfl, totK_node, atot14515, atot14518]
  decide +kernel

theorem arows14529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14529 = true := by
  rw [show D2M8K2.u14529 = KTree.node D2M8K2.u14525 (nat_lit 31516279) (nat_lit 2354013090) (nat_lit 0) D2M8K2.u14528 from rfl, allE_node, arows14525, irow14529, arows14528]
  all_goals rfl

theorem atot14529 : totK PD2M8K2 D2M8K2.u14529 = [395397800573, 1902319565305, 2965184756653, 1625830602615, 213817794556, 4720618446, 0, 0] := by
  rw [show D2M8K2.u14529 = KTree.node D2M8K2.u14525 (nat_lit 31516279) (nat_lit 2354013090) (nat_lit 0) D2M8K2.u14528 from rfl, totK_node, atot14525, atot14528]
  decide +kernel

theorem arows14536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14536 = true := by
  rw [show D2M8K2.u14536 = KTree.node D2M8K2.u14532 (nat_lit 31525083) (nat_lit 3766489105) (nat_lit 0) D2M8K2.u14535 from rfl, allE_node, arows14532, irow14536, arows14535]
  all_goals rfl

theorem atot14536 : totK PD2M8K2 D2M8K2.u14536 = [832074585741, 2860858208532, 2787859481752, 768492746438, 38765675887, 0, 0, 0] := by
  rw [show D2M8K2.u14536 = KTree.node D2M8K2.u14532 (nat_lit 31525083) (nat_lit 3766489105) (nat_lit 0) D2M8K2.u14535 from rfl, totK_node, atot14532, atot14535]
  decide +kernel

theorem arows14544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14544 = true := by
  rw [show D2M8K2.u14544 = KTree.node D2M8K2.u14540 (nat_lit 31534853) (nat_lit 2331823436) (nat_lit 0) D2M8K2.u14543 from rfl, allE_node, arows14540, irow14544, arows14543]
  all_goals rfl

theorem atot14544 : totK PD2M8K2 D2M8K2.u14544 = [424188206739, 2084155369083, 3130538756935, 1329891654944, 119185698086, 1138244013, 0, 0] := by
  rw [show D2M8K2.u14544 = KTree.node D2M8K2.u14540 (nat_lit 31534853) (nat_lit 2331823436) (nat_lit 0) D2M8K2.u14543 from rfl, totK_node, atot14540, atot14543]
  decide +kernel

theorem arows14551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14551 = true := by
  rw [show D2M8K2.u14551 = KTree.node D2M8K2.u14547 (nat_lit 31551022) (nat_lit 3250156797) (nat_lit 0) D2M8K2.u14550 from rfl, allE_node, arows14547, irow14551, arows14550]
  all_goals rfl

theorem atot14551 : totK PD2M8K2 D2M8K2.u14551 = [0, 1251958682099, 3559512295949, 2148696351900, 206407835965, 1095107716, 0, 0] := by
  rw [show D2M8K2.u14551 = KTree.node D2M8K2.u14547 (nat_lit 31551022) (nat_lit 3250156797) (nat_lit 0) D2M8K2.u14550 from rfl, totK_node, atot14547, atot14550]
  decide +kernel

theorem arows14560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14560 = true := by
  rw [show D2M8K2.u14560 = KTree.node D2M8K2.u14556 (nat_lit 31563364) (nat_lit 3747915636) (nat_lit 0) D2M8K2.u14559 from rfl, allE_node, arows14556, irow14560, arows14559]
  all_goals rfl

theorem atot14560 : totK PD2M8K2 D2M8K2.u14560 = [827918221941, 2791014227970, 2633449371067, 853877646079, 128519153072, 3882006667, 0, 0] := by
  rw [show D2M8K2.u14560 = KTree.node D2M8K2.u14556 (nat_lit 31563364) (nat_lit 3747915636) (nat_lit 0) D2M8K2.u14559 from rfl, totK_node, atot14556, atot14559]
  decide +kernel

theorem arows14567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14567 = true := by
  rw [show D2M8K2.u14567 = KTree.node D2M8K2.u14563 (nat_lit 31570312) (nat_lit 3826614521) (nat_lit 0) D2M8K2.u14566 from rfl, allE_node, arows14563, irow14567, arows14566]
  all_goals rfl

theorem atot14567 : totK PD2M8K2 D2M8K2.u14567 = [771894046360, 2817540189997, 2916581702303, 739927118833, 29500998496, 0, 0, 0] := by
  rw [show D2M8K2.u14567 = KTree.node D2M8K2.u14563 (nat_lit 31570312) (nat_lit 3826614521) (nat_lit 0) D2M8K2.u14566 from rfl, totK_node, atot14563, atot14566]
  decide +kernel

theorem arows14575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14575 = true := by
  rw [show D2M8K2.u14575 = KTree.node D2M8K2.u14571 (nat_lit 31580093) (nat_lit 1668102493) (nat_lit 0) D2M8K2.u14574 from rfl, allE_node, arows14571, irow14575, arows14574]
  all_goals rfl

theorem atot14575 : totK PD2M8K2 D2M8K2.u14575 = [443036656631, 2073460830944, 3107647478056, 1449160128389, 131816749186, 1310285577, 0, 0] := by
  rw [show D2M8K2.u14575 = KTree.node D2M8K2.u14571 (nat_lit 31580093) (nat_lit 1668102493) (nat_lit 0) D2M8K2.u14574 from rfl, totK_node, atot14571, atot14574]
  decide +kernel

theorem arows14582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14582 = true := by
  rw [show D2M8K2.u14582 = KTree.node D2M8K2.u14578 (nat_lit 31588567) (nat_lit 1083601075) (nat_lit 0) D2M8K2.u14581 from rfl, allE_node, arows14578, irow14582, arows14581]
  all_goals rfl

theorem atot14582 : totK PD2M8K2 D2M8K2.u14582 = [0, 1156626926177, 3382266266162, 2406631006429, 308615043235, 4879840392, 0, 0] := by
  rw [show D2M8K2.u14582 = KTree.node D2M8K2.u14578 (nat_lit 31588567) (nat_lit 1083601075) (nat_lit 0) D2M8K2.u14581 from rfl, totK_node, atot14578, atot14581]
  decide +kernel

theorem arows14594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14594 = true := by
  rw [show D2M8K2.u14594 = KTree.node D2M8K2.u14590 (nat_lit 31599791) (nat_lit 2779027026) (nat_lit 0) D2M8K2.u14593 from rfl, allE_node, arows14590, irow14594, arows14593]
  all_goals rfl

theorem atot14594 : totK PD2M8K2 D2M8K2.u14594 = [0, 817435251012, 2928423967919, 2748353389047, 616237988698, 26682572712, 0, 0] := by
  rw [show D2M8K2.u14594 = KTree.node D2M8K2.u14590 (nat_lit 31599791) (nat_lit 2779027026) (nat_lit 0) D2M8K2.u14593 from rfl, totK_node, atot14590, atot14593]
  decide +kernel

theorem arows14601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14601 = true := by
  rw [show D2M8K2.u14601 = KTree.node D2M8K2.u14597 (nat_lit 31610403) (nat_lit 1667341128) (nat_lit 0) D2M8K2.u14600 from rfl, allE_node, arows14597, irow14601, arows14600]
  all_goals rfl

theorem atot14601 : totK PD2M8K2 D2M8K2.u14601 = [0, 835579119829, 3120109257596, 2809554362609, 412056574887, 3731543444, 0, 0] := by
  rw [show D2M8K2.u14601 = KTree.node D2M8K2.u14597 (nat_lit 31610403) (nat_lit 1667341128) (nat_lit 0) D2M8K2.u14600 from rfl, totK_node, atot14597, atot14600]
  decide +kernel

theorem arows14609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14609 = true := by
  rw [show D2M8K2.u14609 = KTree.node D2M8K2.u14605 (nat_lit 31618087) (nat_lit 2380302534) (nat_lit 0) D2M8K2.u14608 from rfl, allE_node, arows14605, irow14609, arows14608]
  all_goals rfl

theorem atot14609 : totK PD2M8K2 D2M8K2.u14609 = [0, 794504379502, 2918495702688, 2838578687962, 576860181400, 18178349234, 0, 0] := by
  rw [show D2M8K2.u14609 = KTree.node D2M8K2.u14605 (nat_lit 31618087) (nat_lit 2380302534) (nat_lit 0) D2M8K2.u14608 from rfl, totK_node, atot14605, atot14608]
  decide +kernel

theorem arows14616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14616 = true := by
  rw [show D2M8K2.u14616 = KTree.node D2M8K2.u14612 (nat_lit 31625330) (nat_lit 2210946231) (nat_lit 0) D2M8K2.u14615 from rfl, allE_node, arows14612, irow14616, arows14615]
  all_goals rfl

theorem atot14616 : totK PD2M8K2 D2M8K2.u14616 = [0, 0, 1301289593823, 3624450474520, 1875917916976, 157026213180, 1310517177, 0] := by
  rw [show D2M8K2.u14616 = KTree.node D2M8K2.u14612 (nat_lit 31625330) (nat_lit 2210946231) (nat_lit 0) D2M8K2.u14615 from rfl, totK_node, atot14612, atot14615]
  decide +kernel

theorem arows14625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14625 = true := by
  rw [show D2M8K2.u14625 = KTree.node D2M8K2.u14621 (nat_lit 31646965) (nat_lit 1028531968) (nat_lit 0) D2M8K2.u14624 from rfl, allE_node, arows14621, irow14625, arows14624]
  all_goals rfl

theorem atot14625 : totK PD2M8K2 D2M8K2.u14625 = [0, 442471962879, 2274759300628, 3265461747173, 1159867593439, 64468699372, 0, 0] := by
  rw [show D2M8K2.u14625 = KTree.node D2M8K2.u14621 (nat_lit 31646965) (nat_lit 1028531968) (nat_lit 0) D2M8K2.u14624 from rfl, totK_node, atot14621, atot14624]
  decide +kernel

theorem arows14632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14632 = true := by
  rw [show D2M8K2.u14632 = KTree.node D2M8K2.u14628 (nat_lit 31653631) (nat_lit 2334025651) (nat_lit 0) D2M8K2.u14631 from rfl, allE_node, arows14628, irow14632, arows14631]
  all_goals rfl

theorem atot14632 : totK PD2M8K2 D2M8K2.u14632 = [0, 756136215668, 2782169673980, 2940610490182, 747550557288, 26724469595, 0, 0] := by
  rw [show D2M8K2.u14632 = KTree.node D2M8K2.u14628 (nat_lit 31653631) (nat_lit 2334025651) (nat_lit 0) D2M8K2.u14631 from rfl, totK_node, atot14628, atot14631]
  decide +kernel

theorem arows14640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14640 = true := by
  rw [show D2M8K2.u14640 = KTree.node D2M8K2.u14636 (nat_lit 31660804) (nat_lit 3568301434) (nat_lit 0) D2M8K2.u14639 from rfl, allE_node, arows14636, irow14640, arows14639]
  all_goals rfl

theorem atot14640 : totK PD2M8K2 D2M8K2.u14640 = [0, 872944424306, 2966842818185, 2778229522821, 622862934594, 21707210787, 0, 0] := by
  rw [show D2M8K2.u14640 = KTree.node D2M8K2.u14636 (nat_lit 31660804) (nat_lit 3568301434) (nat_lit 0) D2M8K2.u14639 from rfl, totK_node, atot14636, atot14639]
  decide +kernel

theorem arows14647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14647 = true := by
  rw [show D2M8K2.u14647 = KTree.node D2M8K2.u14643 (nat_lit 31730139) (nat_lit 3765844345) (nat_lit 0) D2M8K2.u14646 from rfl, allE_node, arows14643, irow14647, arows14646]
  all_goals rfl

theorem atot14647 : totK PD2M8K2 D2M8K2.u14647 = [0, 763685286777, 2858204053600, 2853496463726, 667355780144, 26372468781, 0, 0] := by
  rw [show D2M8K2.u14647 = KTree.node D2M8K2.u14643 (nat_lit 31730139) (nat_lit 3765844345) (nat_lit 0) D2M8K2.u14646 from rfl, totK_node, atot14643, atot14646]
  decide +kernel

theorem arows14657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14657 = true := by
  rw [show D2M8K2.u14657 = KTree.node D2M8K2.u14653 (nat_lit 31739494) (nat_lit 1114896976) (nat_lit 0) D2M8K2.u14656 from rfl, allE_node, arows14653, irow14657, arows14656]
  all_goals rfl

theorem atot14657 : totK PD2M8K2 D2M8K2.u14657 = [0, 844328218498, 2996456335796, 2783910952744, 553421636340, 19495044990, 0, 0] := by
  rw [show D2M8K2.u14657 = KTree.node D2M8K2.u14653 (nat_lit 31739494) (nat_lit 1114896976) (nat_lit 0) D2M8K2.u14656 from rfl, totK_node, atot14653, atot14656]
  decide +kernel

theorem arows14664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14664 = true := by
  rw [show D2M8K2.u14664 = KTree.node D2M8K2.u14660 (nat_lit 31746534) (nat_lit 3754526149) (nat_lit 0) D2M8K2.u14663 from rfl, allE_node, arows14660, irow14664, arows14663]
  all_goals rfl

theorem atot14664 : totK PD2M8K2 D2M8K2.u14664 = [0, 423605550748, 1935690394717, 3061932099290, 1478375076856, 141153196095, 1217496766, 0] := by
  rw [show D2M8K2.u14664 = KTree.node D2M8K2.u14660 (nat_lit 31746534) (nat_lit 3754526149) (nat_lit 0) D2M8K2.u14663 from rfl, totK_node, atot14660, atot14663]
  decide +kernel

theorem arows14672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14672 = true := by
  rw [show D2M8K2.u14672 = KTree.node D2M8K2.u14668 (nat_lit 31758666) (nat_lit 3855083236) (nat_lit 0) D2M8K2.u14671 from rfl, allE_node, arows14668, irow14672, arows14671]
  all_goals rfl

theorem atot14672 : totK PD2M8K2 D2M8K2.u14672 = [0, 0, 1192465862001, 3340493507682, 2185269653353, 363356911249, 13105450397, 0] := by
  rw [show D2M8K2.u14672 = KTree.node D2M8K2.u14668 (nat_lit 31758666) (nat_lit 3855083236) (nat_lit 0) D2M8K2.u14671 from rfl, totK_node, atot14668, atot14671]
  decide +kernel

theorem arows14679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14679 = true := by
  rw [show D2M8K2.u14679 = KTree.node D2M8K2.u14675 (nat_lit 31767668) (nat_lit 3652605966) (nat_lit 0) D2M8K2.u14678 from rfl, allE_node, arows14675, irow14679, arows14678]
  all_goals rfl

theorem atot14679 : totK PD2M8K2 D2M8K2.u14679 = [0, 542119350841, 2156202089580, 2848847388610, 1325305238126, 179733436503, 4630915822, 0] := by
  rw [show D2M8K2.u14679 = KTree.node D2M8K2.u14675 (nat_lit 31767668) (nat_lit 3652605966) (nat_lit 0) D2M8K2.u14678 from rfl, totK_node, atot14675, atot14678]
  decide +kernel

theorem arows14688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14688 = true := by
  rw [show D2M8K2.u14688 = KTree.node D2M8K2.u14684 (nat_lit 31778308) (nat_lit 3522061888) (nat_lit 0) D2M8K2.u14687 from rfl, allE_node, arows14684, irow14688, arows14687]
  all_goals rfl

theorem atot14688 : totK PD2M8K2 D2M8K2.u14688 = [0, 767473376774, 2851545231484, 2850894098893, 722185217854, 28317017934, 0, 0] := by
  rw [show D2M8K2.u14688 = KTree.node D2M8K2.u14684 (nat_lit 31778308) (nat_lit 3522061888) (nat_lit 0) D2M8K2.u14687 from rfl, totK_node, atot14684, atot14687]
  decide +kernel

theorem arows14695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14695 = true := by
  rw [show D2M8K2.u14695 = KTree.node D2M8K2.u14691 (nat_lit 31788877) (nat_lit 1386273304) (nat_lit 0) D2M8K2.u14694 from rfl, allE_node, arows14691, irow14695, arows14694]
  all_goals rfl

theorem atot14695 : totK PD2M8K2 D2M8K2.u14695 = [0, 340115668443, 1983827824514, 3260771618440, 1383841781391, 107273987272, 1138244013, 0] := by
  rw [show D2M8K2.u14695 = KTree.node D2M8K2.u14691 (nat_lit 31788877) (nat_lit 1386273304) (nat_lit 0) D2M8K2.u14694 from rfl, totK_node, atot14691, atot14694]
  decide +kernel

theorem arows14703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14703 = true := by
  rw [show D2M8K2.u14703 = KTree.node D2M8K2.u14699 (nat_lit 31802949) (nat_lit 1471370634) (nat_lit 0) D2M8K2.u14702 from rfl, allE_node, arows14699, irow14703, arows14702]
  all_goals rfl

theorem atot14703 : totK PD2M8K2 D2M8K2.u14703 = [0, 318670901333, 1702857408289, 3063444151530, 1717518864094, 209798063891, 4914284239, 0] := by
  rw [show D2M8K2.u14703 = KTree.node D2M8K2.u14699 (nat_lit 31802949) (nat_lit 1471370634) (nat_lit 0) D2M8K2.u14702 from rfl, totK_node, atot14699, atot14702]
  decide +kernel

theorem arows14710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14710 = true := by
  rw [show D2M8K2.u14710 = KTree.node D2M8K2.u14706 (nat_lit 31813982) (nat_lit 3889182706) (nat_lit 0) D2M8K2.u14709 from rfl, allE_node, arows14706, irow14710, arows14709]
  all_goals rfl

theorem atot14710 : totK PD2M8K2 D2M8K2.u14710 = [0, 767177784964, 2832105302024, 2896051886340, 737629701607, 34173758408, 0, 0] := by
  rw [show D2M8K2.u14710 = KTree.node D2M8K2.u14706 (nat_lit 31813982) (nat_lit 3889182706) (nat_lit 0) D2M8K2.u14709 from rfl, totK_node, atot14706, atot14709]
  decide +kernel

theorem arows14721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14721 = true := by
  rw [show D2M8K2.u14721 = KTree.node D2M8K2.u14717 (nat_lit 31820981) (nat_lit 1746268834) (nat_lit 0) D2M8K2.u14720 from rfl, allE_node, arows14717, irow14721, arows14720]
  all_goals rfl

theorem atot14721 : totK PD2M8K2 D2M8K2.u14721 = [0, 878134122414, 2992706801780, 2781870908835, 578857548606, 18355905988, 0, 0] := by
  rw [show D2M8K2.u14721 = KTree.node D2M8K2.u14717 (nat_lit 31820981) (nat_lit 1746268834) (nat_lit 0) D2M8K2.u14720 from rfl, totK_node, atot14717, atot14720]
  decide +kernel

theorem arows14728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14728 = true := by
  rw [show D2M8K2.u14728 = KTree.node D2M8K2.u14724 (nat_lit 32349295) (nat_lit 2347748309) (nat_lit 0) D2M8K2.u14727 from rfl, allE_node, arows14724, irow14728, arows14727]
  all_goals rfl

theorem atot14728 : totK PD2M8K2 D2M8K2.u14728 = [755379393932, 2351292083414, 2315971909038, 1364430582107, 414979803591, 21982715828, 0, 0] := by
  rw [show D2M8K2.u14728 = KTree.node D2M8K2.u14724 (nat_lit 32349295) (nat_lit 2347748309) (nat_lit 0) D2M8K2.u14727 from rfl, totK_node, atot14724, atot14727]
  decide +kernel

theorem arows14736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14736 = true := by
  rw [show D2M8K2.u14736 = KTree.node D2M8K2.u14732 (nat_lit 32359745) (nat_lit 2180501398) (nat_lit 0) D2M8K2.u14735 from rfl, allE_node, arows14732, irow14736, arows14735]
  all_goals rfl

theorem atot14736 : totK PD2M8K2 D2M8K2.u14736 = [763720506556, 2832433338985, 2832659807979, 670014494478, 26300412495, 0, 0, 0] := by
  rw [show D2M8K2.u14736 = KTree.node D2M8K2.u14732 (nat_lit 32359745) (nat_lit 2180501398) (nat_lit 0) D2M8K2.u14735 from rfl, totK_node, atot14732, atot14735]
  decide +kernel

theorem arows14743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14743 = true := by
  rw [show D2M8K2.u14743 = KTree.node D2M8K2.u14739 (nat_lit 32367162) (nat_lit 3374385639) (nat_lit 0) D2M8K2.u14742 from rfl, allE_node, arows14739, irow14743, arows14742]
  all_goals rfl

theorem atot14743 : totK PD2M8K2 D2M8K2.u14743 = [481759246045, 2379693225483, 3214834619787, 1013286041145, 48846355329, 0, 0, 0] := by
  rw [show D2M8K2.u14743 = KTree.node D2M8K2.u14739 (nat_lit 32367162) (nat_lit 3374385639) (nat_lit 0) D2M8K2.u14742 from rfl, totK_node, atot14739, atot14742]
  decide +kernel

theorem arows14752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14752 = true := by
  rw [show D2M8K2.u14752 = KTree.node D2M8K2.u14748 (nat_lit 32377474) (nat_lit 3922929996) (nat_lit 0) D2M8K2.u14751 from rfl, allE_node, arows14748, irow14752, arows14751]
  all_goals rfl

theorem atot14752 : totK PD2M8K2 D2M8K2.u14752 = [0, 1204343572289, 3523178203013, 2129503101162, 214826916263, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14752 = KTree.node D2M8K2.u14748 (nat_lit 32377474) (nat_lit 3922929996) (nat_lit 0) D2M8K2.u14751 from rfl, totK_node, atot14748, atot14751]
  decide +kernel

theorem arows14759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14759 = true := by
  rw [show D2M8K2.u14759 = KTree.node D2M8K2.u14755 (nat_lit 32394313) (nat_lit 1224802125) (nat_lit 0) D2M8K2.u14758 from rfl, allE_node, arows14755, irow14759, arows14758]
  all_goals rfl

theorem atot14759 : totK PD2M8K2 D2M8K2.u14759 = [601719591565, 2409191384031, 3059356616766, 1180362300971, 70159452318, 0, 0, 0] := by
  rw [show D2M8K2.u14759 = KTree.node D2M8K2.u14755 (nat_lit 32394313) (nat_lit 1224802125) (nat_lit 0) D2M8K2.u14758 from rfl, totK_node, atot14755, atot14758]
  decide +kernel

theorem arows14767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14767 = true := by
  rw [show D2M8K2.u14767 = KTree.node D2M8K2.u14763 (nat_lit 32400525) (nat_lit 1157334358) (nat_lit 0) D2M8K2.u14766 from rfl, allE_node, arows14763, irow14767, arows14766]
  all_goals rfl

theorem atot14767 : totK PD2M8K2 D2M8K2.u14767 = [812972746584, 2865372896209, 2869286693748, 667448164513, 25982599253, 0, 0, 0] := by
  rw [show D2M8K2.u14767 = KTree.node D2M8K2.u14763 (nat_lit 32400525) (nat_lit 1157334358) (nat_lit 0) D2M8K2.u14766 from rfl, totK_node, atot14763, atot14766]
  decide +kernel

theorem arows14774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14774 = true := by
  rw [show D2M8K2.u14774 = KTree.node D2M8K2.u14770 (nat_lit 32407951) (nat_lit 2349614553) (nat_lit 0) D2M8K2.u14773 from rfl, allE_node, arows14770, irow14774, arows14773]
  all_goals rfl

theorem atot14774 : totK PD2M8K2 D2M8K2.u14774 = [616498284742, 2659709178529, 3061893596781, 901271036098, 53240712969, 0, 0, 0] := by
  rw [show D2M8K2.u14774 = KTree.node D2M8K2.u14770 (nat_lit 32407951) (nat_lit 2349614553) (nat_lit 0) D2M8K2.u14773 from rfl, totK_node, atot14770, atot14773]
  decide +kernel

theorem arows14784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14784 = true := by
  rw [show D2M8K2.u14784 = KTree.node D2M8K2.u14780 (nat_lit 32417650) (nat_lit 3801631504) (nat_lit 0) D2M8K2.u14783 from rfl, allE_node, arows14780, irow14784, arows14783]
  all_goals rfl

theorem atot14784 : totK PD2M8K2 D2M8K2.u14784 = [0, 747591146744, 2786376238171, 2851254853974, 792520372885, 42081742489, 0, 0] := by
  rw [show D2M8K2.u14784 = KTree.node D2M8K2.u14780 (nat_lit 32417650) (nat_lit 3801631504) (nat_lit 0) D2M8K2.u14783 from rfl, totK_node, atot14780, atot14783]
  decide +kernel

theorem arows14791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14791 = true := by
  rw [show D2M8K2.u14791 = KTree.node D2M8K2.u14787 (nat_lit 32424922) (nat_lit 2541166495) (nat_lit 0) D2M8K2.u14790 from rfl, allE_node, arows14787, irow14791, arows14790]
  all_goals rfl

theorem atot14791 : totK PD2M8K2 D2M8K2.u14791 = [0, 925660797513, 3159997713618, 2723515341627, 448406656385, 6634014755, 0, 0] := by
  rw [show D2M8K2.u14791 = KTree.node D2M8K2.u14787 (nat_lit 32424922) (nat_lit 2541166495) (nat_lit 0) D2M8K2.u14790 from rfl, totK_node, atot14787, atot14790]
  decide +kernel

theorem arows14799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14799 = true := by
  rw [show D2M8K2.u14799 = KTree.node D2M8K2.u14795 (nat_lit 32432555) (nat_lit 2942248401) (nat_lit 0) D2M8K2.u14798 from rfl, allE_node, arows14795, irow14799, arows14798]
  all_goals rfl

theorem atot14799 : totK PD2M8K2 D2M8K2.u14799 = [825785585047, 2522538382914, 2379820554542, 1187511963566, 287136847294, 9302370699, 0, 0] := by
  rw [show D2M8K2.u14799 = KTree.node D2M8K2.u14795 (nat_lit 32432555) (nat_lit 2942248401) (nat_lit 0) D2M8K2.u14798 from rfl, totK_node, atot14795, atot14798]
  decide +kernel

theorem arows14806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14806 = true := by
  rw [show D2M8K2.u14806 = KTree.node D2M8K2.u14802 (nat_lit 32439180) (nat_lit 3547585367) (nat_lit 0) D2M8K2.u14805 from rfl, allE_node, arows14802, irow14806, arows14805]
  all_goals rfl

theorem atot14806 : totK PD2M8K2 D2M8K2.u14806 = [691822965546, 2631363175487, 2958359230896, 920621404740, 50459287437, 0, 0, 0] := by
  rw [show D2M8K2.u14806 = KTree.node D2M8K2.u14802 (nat_lit 32439180) (nat_lit 3547585367) (nat_lit 0) D2M8K2.u14805 from rfl, totK_node, atot14802, atot14805]
  decide +kernel

theorem arows14815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14815 = true := by
  rw [show D2M8K2.u14815 = KTree.node D2M8K2.u14811 (nat_lit 32449974) (nat_lit 3663781720) (nat_lit 0) D2M8K2.u14814 from rfl, allE_node, arows14811, irow14815, arows14814]
  all_goals rfl

theorem atot14815 : totK PD2M8K2 D2M8K2.u14815 = [500634718716, 2427975860477, 3213017523004, 980089908027, 41843439738, 0, 0, 0] := by
  rw [show D2M8K2.u14815 = KTree.node D2M8K2.u14811 (nat_lit 32449974) (nat_lit 3663781720) (nat_lit 0) D2M8K2.u14814 from rfl, totK_node, atot14811, atot14814]
  decide +kernel

theorem arows14822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14822 = true := by
  rw [show D2M8K2.u14822 = KTree.node D2M8K2.u14818 (nat_lit 32457003) (nat_lit 3494222084) (nat_lit 0) D2M8K2.u14821 from rfl, allE_node, arows14818, irow14822, arows14821]
  all_goals rfl

theorem atot14822 : totK PD2M8K2 D2M8K2.u14822 = [0, 932113162035, 3156594255470, 2580695182128, 445102317856, 14222663156, 0, 0] := by
  rw [show D2M8K2.u14822 = KTree.node D2M8K2.u14818 (nat_lit 32457003) (nat_lit 3494222084) (nat_lit 0) D2M8K2.u14821 from rfl, totK_node, atot14818, atot14821]
  decide +kernel

theorem arows14830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14830 = true := by
  rw [show D2M8K2.u14830 = KTree.node D2M8K2.u14826 (nat_lit 32469625) (nat_lit 967246777) (nat_lit 0) D2M8K2.u14829 from rfl, allE_node, arows14826, irow14830, arows14829]
  all_goals rfl

theorem atot14830 : totK PD2M8K2 D2M8K2.u14830 = [407248351753, 1863572531194, 2933298711115, 1705536887014, 221401545470, 4574395652, 0, 0] := by
  rw [show D2M8K2.u14830 = KTree.node D2M8K2.u14826 (nat_lit 32469625) (nat_lit 967246777) (nat_lit 0) D2M8K2.u14829 from rfl, totK_node, atot14826, atot14829]
  decide +kernel

theorem arows14837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14837 = true := by
  rw [show D2M8K2.u14837 = KTree.node D2M8K2.u14833 (nat_lit 32478295) (nat_lit 2188946791) (nat_lit 0) D2M8K2.u14836 from rfl, allE_node, arows14833, irow14837, arows14836]
  all_goals rfl

theorem atot14837 : totK PD2M8K2 D2M8K2.u14837 = [858704757222, 2875585463371, 2766928542004, 756181531346, 38777397440, 0, 0, 0] := by
  rw [show D2M8K2.u14837 = KTree.node D2M8K2.u14833 (nat_lit 32478295) (nat_lit 2188946791) (nat_lit 0) D2M8K2.u14836 from rfl, totK_node, atot14833, atot14836]
  decide +kernel

theorem arows14850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14850 = true := by
  rw [show D2M8K2.u14850 = KTree.node D2M8K2.u14846 (nat_lit 32488207) (nat_lit 2414250667) (nat_lit 0) D2M8K2.u14849 from rfl, allE_node, arows14846, irow14850, arows14849]
  all_goals rfl

theorem atot14850 : totK PD2M8K2 D2M8K2.u14850 = [752797281591, 2864777515775, 2941299713919, 642534134136, 19499939523, 0, 0, 0] := by
  rw [show D2M8K2.u14850 = KTree.node D2M8K2.u14846 (nat_lit 32488207) (nat_lit 2414250667) (nat_lit 0) D2M8K2.u14849 from rfl, totK_node, atot14846, atot14849]
  decide +kernel

theorem arows14857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14857 = true := by
  rw [show D2M8K2.u14857 = KTree.node D2M8K2.u14853 (nat_lit 32495164) (nat_lit 3554738997) (nat_lit 0) D2M8K2.u14856 from rfl, allE_node, arows14853, irow14857, arows14856]
  all_goals rfl

theorem atot14857 : totK PD2M8K2 D2M8K2.u14857 = [0, 1294338418511, 3565896025746, 2104064206347, 193735572931, 1239866073, 0, 0] := by
  rw [show D2M8K2.u14857 = KTree.node D2M8K2.u14853 (nat_lit 32495164) (nat_lit 3554738997) (nat_lit 0) D2M8K2.u14856 from rfl, totK_node, atot14853, atot14856]
  decide +kernel

theorem arows14865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14865 = true := by
  rw [show D2M8K2.u14865 = KTree.node D2M8K2.u14861 (nat_lit 32507406) (nat_lit 3671583058) (nat_lit 0) D2M8K2.u14864 from rfl, allE_node, arows14861, irow14865, arows14864]
  all_goals rfl

theorem atot14865 : totK PD2M8K2 D2M8K2.u14865 = [0, 894420690100, 3041387663263, 2645430193947, 505152408708, 17826068843, 0, 0] := by
  rw [show D2M8K2.u14865 = KTree.node D2M8K2.u14861 (nat_lit 32507406) (nat_lit 3671583058) (nat_lit 0) D2M8K2.u14864 from rfl, totK_node, atot14861, atot14864]
  decide +kernel

theorem arows14872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14872 = true := by
  rw [show D2M8K2.u14872 = KTree.node D2M8K2.u14868 (nat_lit 32558158) (nat_lit 3777273073) (nat_lit 0) D2M8K2.u14871 from rfl, allE_node, arows14868, irow14872, arows14871]
  all_goals rfl

theorem atot14872 : totK PD2M8K2 D2M8K2.u14872 = [844463631107, 2905763485313, 2738598712276, 738655447182, 47683745299, 0, 0, 0] := by
  rw [show D2M8K2.u14872 = KTree.node D2M8K2.u14868 (nat_lit 32558158) (nat_lit 3777273073) (nat_lit 0) D2M8K2.u14871 from rfl, totK_node, atot14868, atot14871]
  decide +kernel

theorem arows14881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14881 = true := by
  rw [show D2M8K2.u14881 = KTree.node D2M8K2.u14877 (nat_lit 32564376) (nat_lit 3418602156) (nat_lit 0) D2M8K2.u14880 from rfl, allE_node, arows14877, irow14881, arows14880]
  all_goals rfl

theorem atot14881 : totK PD2M8K2 D2M8K2.u14881 = [844254808330, 2896870821825, 2796321755725, 684080882881, 25993454863, 0, 0, 0] := by
  rw [show D2M8K2.u14881 = KTree.node D2M8K2.u14877 (nat_lit 32564376) (nat_lit 3418602156) (nat_lit 0) D2M8K2.u14880 from rfl, totK_node, atot14877, atot14880]
  decide +kernel

theorem arows14888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14888 = true := by
  rw [show D2M8K2.u14888 = KTree.node D2M8K2.u14884 (nat_lit 32574474) (nat_lit 3561661891) (nat_lit 0) D2M8K2.u14887 from rfl, allE_node, arows14884, irow14888, arows14887]
  all_goals rfl

theorem atot14888 : totK PD2M8K2 D2M8K2.u14888 = [448209323343, 2304645171553, 3327057573589, 1095019518189, 45555000528, 0, 0, 0] := by
  rw [show D2M8K2.u14888 = KTree.node D2M8K2.u14884 (nat_lit 32574474) (nat_lit 3561661891) (nat_lit 0) D2M8K2.u14887 from rfl, totK_node, atot14884, atot14887]
  decide +kernel

theorem arows14896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14896 = true := by
  rw [show D2M8K2.u14896 = KTree.node D2M8K2.u14892 (nat_lit 32581348) (nat_lit 4000457553) (nat_lit 0) D2M8K2.u14895 from rfl, allE_node, arows14892, irow14896, arows14895]
  all_goals rfl

theorem atot14896 : totK PD2M8K2 D2M8K2.u14896 = [0, 915810566923, 3166393461576, 2720798539928, 384712324908, 6190125969, 0, 0] := by
  rw [show D2M8K2.u14896 = KTree.node D2M8K2.u14892 (nat_lit 32581348) (nat_lit 4000457553) (nat_lit 0) D2M8K2.u14895 from rfl, totK_node, atot14892, atot14895]
  decide +kernel

theorem arows14903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14903 = true := by
  rw [show D2M8K2.u14903 = KTree.node D2M8K2.u14899 (nat_lit 32593667) (nat_lit 2975440576) (nat_lit 0) D2M8K2.u14902 from rfl, allE_node, arows14899, irow14903, arows14902]
  all_goals rfl

theorem atot14903 : totK PD2M8K2 D2M8K2.u14903 = [0, 847866499302, 3043222334308, 2747642119532, 518487351309, 13355831902, 0, 0] := by
  rw [show D2M8K2.u14903 = KTree.node D2M8K2.u14899 (nat_lit 32593667) (nat_lit 2975440576) (nat_lit 0) D2M8K2.u14902 from rfl, totK_node, atot14899, atot14902]
  decide +kernel

theorem arows14913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14913 = true := by
  rw [show D2M8K2.u14913 = KTree.node D2M8K2.u14909 (nat_lit 32600246) (nat_lit 3484011487) (nat_lit 0) D2M8K2.u14912 from rfl, allE_node, arows14909, irow14913, arows14912]
  all_goals rfl

theorem atot14913 : totK PD2M8K2 D2M8K2.u14913 = [0, 865713558376, 3024041561700, 2740145549446, 532904351573, 19868699120, 0, 0] := by
  rw [show D2M8K2.u14913 = KTree.node D2M8K2.u14909 (nat_lit 32600246) (nat_lit 3484011487) (nat_lit 0) D2M8K2.u14912 from rfl, totK_node, atot14909, atot14912]
  decide +kernel

theorem arows14920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14920 = true := by
  rw [show D2M8K2.u14920 = KTree.node D2M8K2.u14916 (nat_lit 32610910) (nat_lit 3505885244) (nat_lit 0) D2M8K2.u14919 from rfl, allE_node, arows14916, irow14920, arows14919]
  all_goals rfl

theorem atot14920 : totK PD2M8K2 D2M8K2.u14920 = [0, 958487570786, 3173097325593, 2591437465317, 400311834099, 6325444884, 0, 0] := by
  rw [show D2M8K2.u14920 = KTree.node D2M8K2.u14916 (nat_lit 32610910) (nat_lit 3505885244) (nat_lit 0) D2M8K2.u14919 from rfl, totK_node, atot14916, atot14919]
  decide +kernel

theorem arows14928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14928 = true := by
  rw [show D2M8K2.u14928 = KTree.node D2M8K2.u14924 (nat_lit 32618551) (nat_lit 1058763571) (nat_lit 0) D2M8K2.u14927 from rfl, allE_node, arows14924, irow14928, arows14927]
  all_goals rfl

theorem atot14928 : totK PD2M8K2 D2M8K2.u14928 = [0, 179867083042, 1590138529625, 3395758179870, 1723984061582, 154862447009, 1369150432, 0] := by
  rw [show D2M8K2.u14928 = KTree.node D2M8K2.u14924 (nat_lit 32618551) (nat_lit 1058763571) (nat_lit 0) D2M8K2.u14927 from rfl, totK_node, atot14924, atot14927]
  decide +kernel

theorem arows14935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14935 = true := by
  rw [show D2M8K2.u14935 = KTree.node D2M8K2.u14931 (nat_lit 32632488) (nat_lit 3557993722) (nat_lit 0) D2M8K2.u14934 from rfl, allE_node, arows14931, irow14935, arows14934]
  all_goals rfl

theorem atot14935 : totK PD2M8K2 D2M8K2.u14935 = [0, 182603865993, 1783835201272, 3625280504514, 1433664346477, 60857170125, 0, 0] := by
  rw [show D2M8K2.u14935 = KTree.node D2M8K2.u14931 (nat_lit 32632488) (nat_lit 3557993722) (nat_lit 0) D2M8K2.u14934 from rfl, totK_node, atot14931, atot14934]
  decide +kernel

theorem arows14944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14944 = true := by
  rw [show D2M8K2.u14944 = KTree.node D2M8K2.u14940 (nat_lit 32645514) (nat_lit 3097385575) (nat_lit 0) D2M8K2.u14943 from rfl, allE_node, arows14940, irow14944, arows14943]
  all_goals rfl

theorem atot14944 : totK PD2M8K2 D2M8K2.u14944 = [0, 732124777782, 2673671590869, 2907829475753, 888828607808, 46568406514, 0, 0] := by
  rw [show D2M8K2.u14944 = KTree.node D2M8K2.u14940 (nat_lit 32645514) (nat_lit 3097385575) (nat_lit 0) D2M8K2.u14943 from rfl, totK_node, atot14940, atot14943]
  decide +kernel

theorem arows14951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14951 = true := by
  rw [show D2M8K2.u14951 = KTree.node D2M8K2.u14947 (nat_lit 32652645) (nat_lit 1495181049) (nat_lit 0) D2M8K2.u14950 from rfl, allE_node, arows14947, irow14951, arows14950]
  all_goals rfl

theorem atot14951 : totK PD2M8K2 D2M8K2.u14951 = [0, 932295570235, 3124281119066, 2717280214618, 512046621525, 10608805553, 0, 0] := by
  rw [show D2M8K2.u14951 = KTree.node D2M8K2.u14947 (nat_lit 32652645) (nat_lit 1495181049) (nat_lit 0) D2M8K2.u14950 from rfl, totK_node, atot14947, atot14950]
  decide +kernel

theorem arows14959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14959 = true := by
  rw [show D2M8K2.u14959 = KTree.node D2M8K2.u14955 (nat_lit 32680662) (nat_lit 2742132585) (nat_lit 0) D2M8K2.u14958 from rfl, allE_node, arows14955, irow14959, arows14958]
  all_goals rfl

theorem atot14959 : totK PD2M8K2 D2M8K2.u14959 = [0, 799120142358, 2912170273934, 2836950816267, 614062791327, 23299732490, 0, 0] := by
  rw [show D2M8K2.u14959 = KTree.node D2M8K2.u14955 (nat_lit 32680662) (nat_lit 2742132585) (nat_lit 0) D2M8K2.u14958 from rfl, totK_node, atot14955, atot14958]
  decide +kernel

theorem arows14966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14966 = true := by
  rw [show D2M8K2.u14966 = KTree.node D2M8K2.u14962 (nat_lit 32687210) (nat_lit 4088624459) (nat_lit 0) D2M8K2.u14965 from rfl, allE_node, arows14962, irow14966, arows14965]
  all_goals rfl

theorem atot14966 : totK PD2M8K2 D2M8K2.u14966 = [0, 721344480847, 2677509385506, 2886069328303, 874789742948, 45814559049, 0, 0] := by
  rw [show D2M8K2.u14966 = KTree.node D2M8K2.u14962 (nat_lit 32687210) (nat_lit 4088624459) (nat_lit 0) D2M8K2.u14965 from rfl, totK_node, atot14962, atot14965]
  decide +kernel

theorem arows14977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14977 = true := by
  rw [show D2M8K2.u14977 = KTree.node D2M8K2.u14973 (nat_lit 32697942) (nat_lit 2605467486) (nat_lit 0) D2M8K2.u14976 from rfl, allE_node, arows14973, irow14977, arows14976]
  all_goals rfl

theorem atot14977 : totK PD2M8K2 D2M8K2.u14977 = [0, 672286054234, 2710360965585, 2999894405112, 767221071994, 29282059853, 0, 0] := by
  rw [show D2M8K2.u14977 = KTree.node D2M8K2.u14973 (nat_lit 32697942) (nat_lit 2605467486) (nat_lit 0) D2M8K2.u14976 from rfl, totK_node, atot14973, atot14976]
  decide +kernel

theorem arows14984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14984 = true := by
  rw [show D2M8K2.u14984 = KTree.node D2M8K2.u14980 (nat_lit 32705652) (nat_lit 2412540562) (nat_lit 0) D2M8K2.u14983 from rfl, allE_node, arows14980, irow14984, arows14983]
  all_goals rfl

theorem atot14984 : totK PD2M8K2 D2M8K2.u14984 = [0, 0, 1071046990327, 3324705520668, 2319519220000, 299270024583, 6301476269, 0] := by
  rw [show D2M8K2.u14984 = KTree.node D2M8K2.u14980 (nat_lit 32705652) (nat_lit 2412540562) (nat_lit 0) D2M8K2.u14983 from rfl, totK_node, atot14980, atot14983]
  decide +kernel

theorem arows14992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14992 = true := by
  rw [show D2M8K2.u14992 = KTree.node D2M8K2.u14988 (nat_lit 32721531) (nat_lit 2847949719) (nat_lit 0) D2M8K2.u14991 from rfl, allE_node, arows14988, irow14992, arows14991]
  all_goals rfl

theorem atot14992 : totK PD2M8K2 D2M8K2.u14992 = [0, 518947284341, 2448743109604, 3162218868615, 960009524845, 49351960072, 0, 0] := by
  rw [show D2M8K2.u14992 = KTree.node D2M8K2.u14988 (nat_lit 32721531) (nat_lit 2847949719) (nat_lit 0) D2M8K2.u14991 from rfl, totK_node, atot14988, atot14991]
  decide +kernel

theorem arows14999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14999 = true := by
  rw [show D2M8K2.u14999 = KTree.node D2M8K2.u14995 (nat_lit 32731798) (nat_lit 3526781802) (nat_lit 0) D2M8K2.u14998 from rfl, allE_node, arows14995, irow14999, arows14998]
  all_goals rfl

theorem atot14999 : totK PD2M8K2 D2M8K2.u14999 = [0, 746114926253, 2709624960548, 2854486499981, 868522321887, 45995583843, 0, 0] := by
  rw [show D2M8K2.u14999 = KTree.node D2M8K2.u14995 (nat_lit 32731798) (nat_lit 3526781802) (nat_lit 0) D2M8K2.u14998 from rfl, totK_node, atot14995, atot14998]
  decide +kernel

theorem arows15008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15008 = true := by
  rw [show D2M8K2.u15008 = KTree.node D2M8K2.u15004 (nat_lit 32739155) (nat_lit 2744439150) (nat_lit 0) D2M8K2.u15007 from rfl, allE_node, arows15004, irow15008, arows15007]
  all_goals rfl

theorem atot15008 : totK PD2M8K2 D2M8K2.u15008 = [0, 751595623571, 2831106643920, 2908271420936, 681279990596, 26893758740, 0, 0] := by
  rw [show D2M8K2.u15008 = KTree.node D2M8K2.u15004 (nat_lit 32739155) (nat_lit 2744439150) (nat_lit 0) D2M8K2.u15007 from rfl, totK_node, atot15004, atot15007]
  decide +kernel

theorem arows15015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15015 = true := by
  rw [show D2M8K2.u15015 = KTree.node D2M8K2.u15011 (nat_lit 32746640) (nat_lit 3506581975) (nat_lit 0) D2M8K2.u15014 from rfl, allE_node, arows15011, irow15015, arows15014]
  all_goals rfl

theorem atot15015 : totK PD2M8K2 D2M8K2.u15015 = [0, 0, 1155356026422, 3432040870022, 2238055678078, 232677966348, 2335892675, 0] := by
  rw [show D2M8K2.u15015 = KTree.node D2M8K2.u15011 (nat_lit 32746640) (nat_lit 3506581975) (nat_lit 0) D2M8K2.u15014 from rfl, totK_node, atot15011, atot15014]
  decide +kernel

theorem arows15023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15023 = true := by
  rw [show D2M8K2.u15023 = KTree.node D2M8K2.u15019 (nat_lit 32761076) (nat_lit 1121126731) (nat_lit 0) D2M8K2.u15022 from rfl, allE_node, arows15019, irow15023, arows15022]
  all_goals rfl

theorem atot15023 : totK PD2M8K2 D2M8K2.u15023 = [0, 494137245386, 2332517570825, 3078328493455, 1105559439354, 120813555338, 4028038878, 0] := by
  rw [show D2M8K2.u15023 = KTree.node D2M8K2.u15019 (nat_lit 32761076) (nat_lit 1121126731) (nat_lit 0) D2M8K2.u15022 from rfl, totK_node, atot15019, atot15022]
  decide +kernel

theorem arows15030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15030 = true := by
  rw [show D2M8K2.u15030 = KTree.node D2M8K2.u15026 (nat_lit 32811006) (nat_lit 3879454023) (nat_lit 0) D2M8K2.u15029 from rfl, allE_node, arows15026, irow15030, arows15029]
  all_goals rfl

theorem atot15030 : totK PD2M8K2 D2M8K2.u15030 = [0, 771247657755, 2779741958393, 2845520204438, 799348102719, 38018906608, 0, 0] := by
  rw [show D2M8K2.u15030 = KTree.node D2M8K2.u15026 (nat_lit 32811006) (nat_lit 3879454023) (nat_lit 0) D2M8K2.u15029 from rfl, totK_node, atot15026, atot15029]
  decide +kernel

theorem arows15040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15040 = true := by
  rw [show D2M8K2.u15040 = KTree.node D2M8K2.u15036 (nat_lit 32817580) (nat_lit 2570011987) (nat_lit 0) D2M8K2.u15039 from rfl, allE_node, arows15036, irow15040, arows15039]
  all_goals rfl

theorem atot15040 : totK PD2M8K2 D2M8K2.u15040 = [0, 869639304998, 3021212391820, 2803879980593, 542856633236, 10871550295, 0, 0] := by
  rw [show D2M8K2.u15040 = KTree.node D2M8K2.u15036 (nat_lit 32817580) (nat_lit 2570011987) (nat_lit 0) D2M8K2.u15039 from rfl, totK_node, atot15036, atot15039]
  decide +kernel

theorem arows15047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15047 = true := by
  rw [show D2M8K2.u15047 = KTree.node D2M8K2.u15043 (nat_lit 32827497) (nat_lit 1651036616) (nat_lit 0) D2M8K2.u15046 from rfl, allE_node, arows15043, irow15047, arows15046]
  all_goals rfl

theorem atot15047 : totK PD2M8K2 D2M8K2.u15047 = [0, 0, 1285489403343, 3556241939783, 2058965552975, 194799845803, 1288491354, 0] := by
  rw [show D2M8K2.u15047 = KTree.node D2M8K2.u15043 (nat_lit 32827497) (nat_lit 1651036616) (nat_lit 0) D2M8K2.u15046 from rfl, totK_node, atot15043, atot15046]
  decide +kernel

theorem arows15055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15055 = true := by
  rw [show D2M8K2.u15055 = KTree.node D2M8K2.u15051 (nat_lit 32836687) (nat_lit 2432917385) (nat_lit 0) D2M8K2.u15054 from rfl, allE_node, arows15051, irow15055, arows15054]
  all_goals rfl

theorem atot15055 : totK PD2M8K2 D2M8K2.u15055 = [0, 0, 918703043222, 3167260075127, 2520097142577, 392219343396, 9625297583, 0] := by
  rw [show D2M8K2.u15055 = KTree.node D2M8K2.u15051 (nat_lit 32836687) (nat_lit 2432917385) (nat_lit 0) D2M8K2.u15054 from rfl, totK_node, atot15051, atot15054]
  decide +kernel

theorem arows15062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15062 = true := by
  rw [show D2M8K2.u15062 = KTree.node D2M8K2.u15058 (nat_lit 32846963) (nat_lit 2938923962) (nat_lit 0) D2M8K2.u15061 from rfl, allE_node, arows15058, irow15062, arows15061]
  all_goals rfl

theorem atot15062 : totK PD2M8K2 D2M8K2.u15062 = [0, 753166441893, 2382429181664, 2339604985515, 1309999425036, 382000077933, 21751168066, 0] := by
  rw [show D2M8K2.u15062 = KTree.node D2M8K2.u15058 (nat_lit 32846963) (nat_lit 2938923962) (nat_lit 0) D2M8K2.u15061 from rfl, totK_node, atot15058, atot15061]
  decide +kernel

theorem arows15071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15071 = true := by
  rw [show D2M8K2.u15071 = KTree.node D2M8K2.u15067 (nat_lit 32857376) (nat_lit 3791176880) (nat_lit 0) D2M8K2.u15070 from rfl, allE_node, arows15067, irow15071, arows15070]
  all_goals rfl

theorem atot15071 : totK PD2M8K2 D2M8K2.u15071 = [0, 763611748897, 2816595759831, 2843847289518, 651144787267, 26300412495, 0, 0] := by
  rw [show D2M8K2.u15071 = KTree.node D2M8K2.u15067 (nat_lit 32857376) (nat_lit 3791176880) (nat_lit 0) D2M8K2.u15070 from rfl, totK_node, atot15067, atot15070]
  decide +kernel

theorem arows15078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15078 = true := by
  rw [show D2M8K2.u15078 = KTree.node D2M8K2.u15074 (nat_lit 32864089) (nat_lit 1490478914) (nat_lit 0) D2M8K2.u15077 from rfl, allE_node, arows15074, irow15078, arows15077]
  all_goals rfl

theorem atot15078 : totK PD2M8K2 D2M8K2.u15078 = [0, 580372692679, 2573246686632, 3123642502001, 848144375192, 36640207665, 0, 0] := by
  rw [show D2M8K2.u15078 = KTree.node D2M8K2.u15074 (nat_lit 32864089) (nat_lit 1490478914) (nat_lit 0) D2M8K2.u15077 from rfl, totK_node, atot15074, atot15077]
  decide +kernel

theorem arows15086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15086 = true := by
  rw [show D2M8K2.u15086 = KTree.node D2M8K2.u15082 (nat_lit 32874657) (nat_lit 1840212400) (nat_lit 0) D2M8K2.u15085 from rfl, allE_node, arows15082, irow15086, arows15085]
  all_goals rfl

theorem atot15086 : totK PD2M8K2 D2M8K2.u15086 = [0, 0, 1231595110447, 3546486988681, 2060548769955, 204176228456, 1369150432, 0] := by
  rw [show D2M8K2.u15086 = KTree.node D2M8K2.u15082 (nat_lit 32874657) (nat_lit 1840212400) (nat_lit 0) D2M8K2.u15085 from rfl, totK_node, atot15082, atot15085]
  decide +kernel

theorem arows15093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15093 = true := by
  rw [show D2M8K2.u15093 = KTree.node D2M8K2.u15089 (nat_lit 32929357) (nat_lit 1386273304) (nat_lit 0) D2M8K2.u15092 from rfl, allE_node, arows15089, irow15093, arows15092]
  all_goals rfl

theorem atot15093 : totK PD2M8K2 D2M8K2.u15093 = [0, 581874992973, 2436383987403, 3077048699306, 1014691482332, 51860185275, 0, 0] := by
  rw [show D2M8K2.u15093 = KTree.node D2M8K2.u15089 (nat_lit 32929357) (nat_lit 1386273304) (nat_lit 0) D2M8K2.u15092 from rfl, totK_node, atot15089, atot15092]
  decide +kernel

theorem arows15105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15105 = true := by
  rw [show D2M8K2.u15105 = KTree.node D2M8K2.u15101 (nat_lit 32936320) (nat_lit 3781001236) (nat_lit 0) D2M8K2.u15104 from rfl, allE_node, arows15101, irow15105, arows15104]
  all_goals rfl

theorem atot15105 : totK PD2M8K2 D2M8K2.u15105 = [0, 759948417333, 2780952524881, 2859301605623, 806330427743, 45068261503, 0, 0] := by
  rw [show D2M8K2.u15105 = KTree.node D2M8K2.u15101 (nat_lit 32936320) (nat_lit 3781001236) (nat_lit 0) D2M8K2.u15104 from rfl, totK_node, atot15101, atot15104]
  decide +kernel

theorem arows15112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15112 = true := by
  rw [show D2M8K2.u15112 = KTree.node D2M8K2.u15108 (nat_lit 32946817) (nat_lit 1419478073) (nat_lit 0) D2M8K2.u15111 from rfl, allE_node, arows15108, irow15112, arows15111]
  all_goals rfl

theorem atot15112 : totK PD2M8K2 D2M8K2.u15112 = [0, 637706250882, 2627685895021, 3047069954315, 838520703789, 36864446645, 0, 0] := by
  rw [show D2M8K2.u15112 = KTree.node D2M8K2.u15108 (nat_lit 32946817) (nat_lit 1419478073) (nat_lit 0) D2M8K2.u15111 from rfl, totK_node, atot15108, atot15111]
  decide +kernel

theorem arows15120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15120 = true := by
  rw [show D2M8K2.u15120 = KTree.node D2M8K2.u15116 (nat_lit 32954447) (nat_lit 2159978722) (nat_lit 0) D2M8K2.u15119 from rfl, allE_node, arows15116, irow15120, arows15119]
  all_goals rfl

theorem atot15120 : totK PD2M8K2 D2M8K2.u15120 = [0, 0, 994234358666, 3293469163359, 2468024105093, 344858049537, 6601594569, 0] := by
  rw [show D2M8K2.u15120 = KTree.node D2M8K2.u15116 (nat_lit 32954447) (nat_lit 2159978722) (nat_lit 0) D2M8K2.u15119 from rfl, totK_node, atot15116, atot15119]
  decide +kernel

theorem arows15127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15127 = true := by
  rw [show D2M8K2.u15127 = KTree.node D2M8K2.u15123 (nat_lit 32968224) (nat_lit 3708958841) (nat_lit 0) D2M8K2.u15126 from rfl, allE_node, arows15123, irow15127, arows15126]
  all_goals rfl

theorem atot15127 : totK PD2M8K2 D2M8K2.u15127 = [0, 419158787481, 2193302007323, 3232788363541, 1248928419387, 75919865027, 0, 0] := by
  rw [show D2M8K2.u15127 = KTree.node D2M8K2.u15123 (nat_lit 32968224) (nat_lit 3708958841) (nat_lit 0) D2M8K2.u15126 from rfl, totK_node, atot15123, atot15126]
  decide +kernel

theorem arows15136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15136 = true := by
  rw [show D2M8K2.u15136 = KTree.node D2M8K2.u15132 (nat_lit 32980678) (nat_lit 3564982458) (nat_lit 0) D2M8K2.u15135 from rfl, allE_node, arows15132, irow15136, arows15135]
  all_goals rfl

theorem atot15136 : totK PD2M8K2 D2M8K2.u15136 = [0, 769119525315, 2771026975039, 2883715629626, 818477683111, 45347243087, 0, 0] := by
  rw [show D2M8K2.u15136 = KTree.node D2M8K2.u15132 (nat_lit 32980678) (nat_lit 3564982458) (nat_lit 0) D2M8K2.u15135 from rfl, totK_node, atot15132, atot15135]
  decide +kernel

theorem arows15143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15143 = true := by
  rw [show D2M8K2.u15143 = KTree.node D2M8K2.u15139 (nat_lit 32987659) (nat_lit 1617497951) (nat_lit 0) D2M8K2.u15142 from rfl, allE_node, arows15139, irow15143, arows15142]
  all_goals rfl

theorem atot15143 : totK PD2M8K2 D2M8K2.u15143 = [0, 795831571512, 2881561384435, 2875559743552, 641143198379, 18447596263, 0, 0] := by
  rw [show D2M8K2.u15143 = KTree.node D2M8K2.u15139 (nat_lit 32987659) (nat_lit 1617497951) (nat_lit 0) D2M8K2.u15142 from rfl, totK_node, atot15139, atot15142]
  decide +kernel

theorem arows15151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15151 = true := by
  rw [show D2M8K2.u15151 = KTree.node D2M8K2.u15147 (nat_lit 32994948) (nat_lit 1449144210) (nat_lit 0) D2M8K2.u15150 from rfl, allE_node, arows15147, irow15151, arows15150]
  all_goals rfl

theorem atot15151 : totK PD2M8K2 D2M8K2.u15151 = [0, 0, 1183937042328, 3501496058561, 2246742137721, 218997803243, 1239866073, 0] := by
  rw [show D2M8K2.u15151 = KTree.node D2M8K2.u15147 (nat_lit 32994948) (nat_lit 1449144210) (nat_lit 0) D2M8K2.u15150 from rfl, totK_node, atot15147, atot15150]
  decide +kernel

theorem arows15158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15158 = true := by
  rw [show D2M8K2.u15158 = KTree.node D2M8K2.u15154 (nat_lit 33008681) (nat_lit 1545277284) (nat_lit 0) D2M8K2.u15157 from rfl, allE_node, arows15154, irow15158, arows15157]
  all_goals rfl

theorem atot15158 : totK PD2M8K2 D2M8K2.u15158 = [0, 420637493945, 1892925147294, 2951884672684, 1671504004985, 230305934931, 5425831197, 0] := by
  rw [show D2M8K2.u15158 = KTree.node D2M8K2.u15154 (nat_lit 33008681) (nat_lit 1545277284) (nat_lit 0) D2M8K2.u15157 from rfl, totK_node, atot15154, atot15157]
  decide +kernel

theorem arows15168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15168 = true := by
  rw [show D2M8K2.u15168 = KTree.node D2M8K2.u15164 (nat_lit 33020680) (nat_lit 3822099201) (nat_lit 0) D2M8K2.u15167 from rfl, allE_node, arows15164, irow15168, arows15167]
  all_goals rfl

theorem atot15168 : totK PD2M8K2 D2M8K2.u15168 = [0, 800504900652, 2949488746313, 2875556965261, 540804096636, 15616951058, 0, 0] := by
  rw [show D2M8K2.u15168 = KTree.node D2M8K2.u15164 (nat_lit 33020680) (nat_lit 3822099201) (nat_lit 0) D2M8K2.u15167 from rfl, totK_node, atot15164, atot15167]
  decide +kernel

theorem arows15175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15175 = true := by
  rw [show D2M8K2.u15175 = KTree.node D2M8K2.u15171 (nat_lit 33027604) (nat_lit 4006101204) (nat_lit 0) D2M8K2.u15174 from rfl, allE_node, arows15171, irow15175, arows15174]
  all_goals rfl

theorem atot15175 : totK PD2M8K2 D2M8K2.u15175 = [0, 423568743631, 2192341845827, 3193410917183, 1178720737284, 104216144473, 1138244013, 0] := by
  rw [show D2M8K2.u15175 = KTree.node D2M8K2.u15171 (nat_lit 33027604) (nat_lit 4006101204) (nat_lit 0) D2M8K2.u15174 from rfl, totK_node, atot15171, atot15174]
  decide +kernel

theorem arows15183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15183 = true := by
  rw [show D2M8K2.u15183 = KTree.node D2M8K2.u15179 (nat_lit 33043980) (nat_lit 3533623431) (nat_lit 0) D2M8K2.u15182 from rfl, allE_node, arows15179, irow15183, arows15182]
  all_goals rfl

theorem atot15183 : totK PD2M8K2 D2M8K2.u15183 = [0, 194625098643, 1689633691351, 3517284029121, 1621440721854, 89307985716, 0, 0] := by
  rw [show D2M8K2.u15183 = KTree.node D2M8K2.u15179 (nat_lit 33043980) (nat_lit 3533623431) (nat_lit 0) D2M8K2.u15182 from rfl, totK_node, atot15179, atot15182]
  decide +kernel

theorem arows15190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15190 = true := by
  rw [show D2M8K2.u15190 = KTree.node D2M8K2.u15186 (nat_lit 33057643) (nat_lit 1615998974) (nat_lit 0) D2M8K2.u15189 from rfl, allE_node, arows15186, irow15190, arows15189]
  all_goals rfl

theorem atot15190 : totK PD2M8K2 D2M8K2.u15190 = [0, 833403830366, 2922250215316, 2824753344404, 701333337120, 32716181870, 0, 0] := by
  rw [show D2M8K2.u15190 = KTree.node D2M8K2.u15186 (nat_lit 33057643) (nat_lit 1615998974) (nat_lit 0) D2M8K2.u15189 from rfl, totK_node, atot15186, atot15189]
  decide +kernel

theorem arows15199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15199 = true := by
  rw [show D2M8K2.u15199 = KTree.node D2M8K2.u15195 (nat_lit 33064670) (nat_lit 2447936834) (nat_lit 0) D2M8K2.u15198 from rfl, allE_node, arows15195, irow15199, arows15198]
  all_goals rfl

theorem atot15199 : totK PD2M8K2 D2M8K2.u15199 = [0, 829294564905, 2925986814747, 2854502756467, 616587510714, 17725851219, 0, 0] := by
  rw [show D2M8K2.u15199 = KTree.node D2M8K2.u15195 (nat_lit 33064670) (nat_lit 2447936834) (nat_lit 0) D2M8K2.u15198 from rfl, totK_node, atot15195, atot15198]
  decide +kernel

theorem arows15206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15206 = true := by
  rw [show D2M8K2.u15206 = KTree.node D2M8K2.u15202 (nat_lit 33074672) (nat_lit 2642582981) (nat_lit 0) D2M8K2.u15205 from rfl, allE_node, arows15202, irow15206, arows15205]
  all_goals rfl

theorem atot15206 : totK PD2M8K2 D2M8K2.u15206 = [0, 181674658392, 1594439236784, 3342274930799, 1898497056559, 179659211382, 1310285577, 0] := by
  rw [show D2M8K2.u15206 = KTree.node D2M8K2.u15202 (nat_lit 33074672) (nat_lit 2642582981) (nat_lit 0) D2M8K2.u15205 from rfl, totK_node, atot15202, atot15205]
  decide +kernel

theorem arows15214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15214 = true := by
  rw [show D2M8K2.u15214 = KTree.node D2M8K2.u15210 (nat_lit 33083339) (nat_lit 2320752373) (nat_lit 0) D2M8K2.u15213 from rfl, allE_node, arows15210, irow15214, arows15213]
  all_goals rfl

theorem atot15214 : totK PD2M8K2 D2M8K2.u15214 = [0, 0, 933948608711, 3210231846841, 2606301065555, 391224032705, 9811245038, 0] := by
  rw [show D2M8K2.u15214 = KTree.node D2M8K2.u15210 (nat_lit 33083339) (nat_lit 2320752373) (nat_lit 0) D2M8K2.u15213 from rfl, totK_node, atot15210, atot15213]
  decide +kernel

theorem arows15221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15221 = true := by
  rw [show D2M8K2.u15221 = KTree.node D2M8K2.u15217 (nat_lit 33093966) (nat_lit 3691940604) (nat_lit 0) D2M8K2.u15220 from rfl, allE_node, arows15217, irow15221, arows15220]
  all_goals rfl

theorem atot15221 : totK PD2M8K2 D2M8K2.u15221 = [0, 0, 882408247493, 3020427582960, 2703951993372, 571600539894, 23120318498, 0] := by
  rw [show D2M8K2.u15221 = KTree.node D2M8K2.u15217 (nat_lit 33093966) (nat_lit 3691940604) (nat_lit 0) D2M8K2.u15220 from rfl, totK_node, atot15217, atot15220]
  decide +kernel

theorem arows15232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15232 = true := by
  rw [show D2M8K2.u15232 = KTree.node D2M8K2.u15228 (nat_lit 33104540) (nat_lit 3219419801) (nat_lit 0) D2M8K2.u15231 from rfl, allE_node, arows15228, irow15232, arows15231]
  all_goals rfl

theorem atot15232 : totK PD2M8K2 D2M8K2.u15232 = [0, 0, 830146928472, 3040865403890, 2840027616050, 433196717931, 10761034340, 0] := by
  rw [show D2M8K2.u15232 = KTree.node D2M8K2.u15228 (nat_lit 33104540) (nat_lit 3219419801) (nat_lit 0) D2M8K2.u15231 from rfl, totK_node, atot15228, atot15231]
  decide +kernel

theorem arows15239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15239 = true := by
  rw [show D2M8K2.u15239 = KTree.node D2M8K2.u15235 (nat_lit 33112180) (nat_lit 3502857488) (nat_lit 0) D2M8K2.u15238 from rfl, allE_node, arows15235, irow15239, arows15238]
  all_goals rfl

theorem atot15239 : totK PD2M8K2 D2M8K2.u15239 = [0, 0, 816628446623, 2959265688762, 2807041943038, 517758762609, 22868468978, 0] := by
  rw [show D2M8K2.u15239 = KTree.node D2M8K2.u15235 (nat_lit 33112180) (nat_lit 3502857488) (nat_lit 0) D2M8K2.u15238 from rfl, totK_node, atot15235, atot15238]
  decide +kernel

theorem arows15247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15247 = true := by
  rw [show D2M8K2.u15247 = KTree.node D2M8K2.u15243 (nat_lit 33122579) (nat_lit 2879916139) (nat_lit 0) D2M8K2.u15246 from rfl, allE_node, arows15243, irow15247, arows15246]
  all_goals rfl

theorem atot15247 : totK PD2M8K2 D2M8K2.u15247 = [0, 0, 0, 1353523996573, 3665626890271, 1797058274092, 161684381686, 1369150432] := by
  rw [show D2M8K2.u15247 = KTree.node D2M8K2.u15243 (nat_lit 33122579) (nat_lit 2879916139) (nat_lit 0) D2M8K2.u15246 from rfl, totK_node, atot15243, atot15246]
  decide +kernel

theorem arows15254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15254 = true := by
  rw [show D2M8K2.u15254 = KTree.node D2M8K2.u15250 (nat_lit 33178309) (nat_lit 1354964743) (nat_lit 0) D2M8K2.u15253 from rfl, allE_node, arows15250, irow15254, arows15253]
  all_goals rfl

theorem atot15254 : totK PD2M8K2 D2M8K2.u15254 = [0, 0, 595872241218, 2611493714567, 3155106172335, 744653787058, 27203852424, 0] := by
  rw [show D2M8K2.u15254 = KTree.node D2M8K2.u15250 (nat_lit 33178309) (nat_lit 1354964743) (nat_lit 0) D2M8K2.u15253 from rfl, totK_node, atot15250, atot15253]
  decide +kernel

theorem arows15263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15263 = true := by
  rw [show D2M8K2.u15263 = KTree.node D2M8K2.u15259 (nat_lit 33186037) (nat_lit 1189885273) (nat_lit 0) D2M8K2.u15262 from rfl, allE_node, arows15259, irow15263, arows15262]
  all_goals rfl

theorem atot15263 : totK PD2M8K2 D2M8K2.u15263 = [0, 0, 968667204367, 3242457014119, 2651620614584, 388492592818, 6926566070, 0] := by
  rw [show D2M8K2.u15263 = KTree.node D2M8K2.u15259 (nat_lit 33186037) (nat_lit 1189885273) (nat_lit 0) D2M8K2.u15262 from rfl, totK_node, atot15259, atot15262]
  decide +kernel

theorem arows15270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15270 = true := by
  rw [show D2M8K2.u15270 = KTree.node D2M8K2.u15266 (nat_lit 33196949) (nat_lit 2357672697) (nat_lit 0) D2M8K2.u15269 from rfl, allE_node, arows15266, irow15270, arows15269]
  all_goals rfl

theorem atot15270 : totK PD2M8K2 D2M8K2.u15270 = [0, 0, 834123126399, 3002016422427, 2817316223039, 511483340204, 16149957853, 0] := by
  rw [show D2M8K2.u15270 = KTree.node D2M8K2.u15266 (nat_lit 33196949) (nat_lit 2357672697) (nat_lit 0) D2M8K2.u15269 from rfl, totK_node, atot15266, atot15269]
  decide +kernel

theorem arows15278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15278 = true := by
  rw [show D2M8K2.u15278 = KTree.node D2M8K2.u15274 (nat_lit 33229523) (nat_lit 2858976552) (nat_lit 0) D2M8K2.u15277 from rfl, allE_node, arows15274, irow15278, arows15277]
  all_goals rfl

theorem atot15278 : totK PD2M8K2 D2M8K2.u15278 = [0, 0, 802025210151, 3098372703828, 2949446451586, 459716774473, 6971940536, 0] := by
  rw [show D2M8K2.u15278 = KTree.node D2M8K2.u15274 (nat_lit 33229523) (nat_lit 2858976552) (nat_lit 0) D2M8K2.u15277 from rfl, totK_node, atot15274, atot15277]
  decide +kernel

theorem arows15285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15285 = true := by
  rw [show D2M8K2.u15285 = KTree.node D2M8K2.u15281 (nat_lit 33236865) (nat_lit 1647006493) (nat_lit 0) D2M8K2.u15284 from rfl, allE_node, arows15281, irow15285, arows15284]
  all_goals rfl

theorem atot15285 : totK PD2M8K2 D2M8K2.u15285 = [0, 0, 936340517661, 3142337692722, 2679208776149, 441158522937, 14811170984, 0] := by
  rw [show D2M8K2.u15285 = KTree.node D2M8K2.u15281 (nat_lit 33236865) (nat_lit 1647006493) (nat_lit 0) D2M8K2.u15284 from rfl, totK_node, atot15281, atot15284]
  decide +kernel

theorem arows15295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15295 = true := by
  rw [show D2M8K2.u15295 = KTree.node D2M8K2.u15291 (nat_lit 33268155) (nat_lit 3425208046) (nat_lit 0) D2M8K2.u15294 from rfl, allE_node, arows15291, irow15295, arows15294]
  all_goals rfl

theorem atot15295 : totK PD2M8K2 D2M8K2.u15295 = [0, 0, 973274084148, 3282901081670, 2637521616771, 281050339560, 2533470052, 0] := by
  rw [show D2M8K2.u15295 = KTree.node D2M8K2.u15291 (nat_lit 33268155) (nat_lit 3425208046) (nat_lit 0) D2M8K2.u15294 from rfl, totK_node, atot15291, atot15294]
  decide +kernel

theorem arows15302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15302 = true := by
  rw [show D2M8K2.u15302 = KTree.node D2M8K2.u15298 (nat_lit 33275686) (nat_lit 1176387376) (nat_lit 0) D2M8K2.u15301 from rfl, allE_node, arows15298, irow15302, arows15301]
  all_goals rfl

theorem atot15302 : totK PD2M8K2 D2M8K2.u15302 = [0, 0, 911163701139, 3281941939940, 2686724503318, 285939621387, 2294578496, 0] := by
  rw [show D2M8K2.u15302 = KTree.node D2M8K2.u15298 (nat_lit 33275686) (nat_lit 1176387376) (nat_lit 0) D2M8K2.u15301 from rfl, totK_node, atot15298, atot15301]
  decide +kernel

theorem arows15310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15310 = true := by
  rw [show D2M8K2.u15310 = KTree.node D2M8K2.u15306 (nat_lit 33308201) (nat_lit 1089001684) (nat_lit 0) D2M8K2.u15309 from rfl, allE_node, arows15306, irow15310, arows15309]
  all_goals rfl

theorem atot15310 : totK PD2M8K2 D2M8K2.u15310 = [0, 0, 759922326833, 2907027888715, 3015927708490, 599138389785, 16083235428, 0] := by
  rw [show D2M8K2.u15310 = KTree.node D2M8K2.u15306 (nat_lit 33308201) (nat_lit 1089001684) (nat_lit 0) D2M8K2.u15309 from rfl, totK_node, atot15306, atot15309]
  decide +kernel

theorem arows15317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15317 = true := by
  rw [show D2M8K2.u15317 = KTree.node D2M8K2.u15313 (nat_lit 33315559) (nat_lit 2353804635) (nat_lit 0) D2M8K2.u15316 from rfl, allE_node, arows15313, irow15317, arows15316]
  all_goals rfl

theorem atot15317 : totK PD2M8K2 D2M8K2.u15317 = [0, 0, 854316878378, 3063189339333, 2860402182009, 493469441632, 10076216633, 0] := by
  rw [show D2M8K2.u15317 = KTree.node D2M8K2.u15313 (nat_lit 33315559) (nat_lit 2353804635) (nat_lit 0) D2M8K2.u15316 from rfl, totK_node, atot15313, atot15316]
  decide +kernel

theorem arows15326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15326 = true := by
  rw [show D2M8K2.u15326 = KTree.node D2M8K2.u15322 (nat_lit 33390819) (nat_lit 3655373328) (nat_lit 0) D2M8K2.u15325 from rfl, allE_node, arows15322, irow15326, arows15325]
  all_goals rfl

theorem atot15326 : totK PD2M8K2 D2M8K2.u15326 = [0, 869549231262, 2684574580793, 2474435110103, 1020761192320, 237643973716, 17014456371, 0] := by
  rw [show D2M8K2.u15326 = KTree.node D2M8K2.u15322 (nat_lit 33390819) (nat_lit 3655373328) (nat_lit 0) D2M8K2.u15325 from rfl, totK_node, atot15322, atot15325]
  decide +kernel

theorem arows15333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15333 = true := by
  rw [show D2M8K2.u15333 = KTree.node D2M8K2.u15329 (nat_lit 33396976) (nat_lit 3417701625) (nat_lit 0) D2M8K2.u15332 from rfl, allE_node, arows15329, irow15333, arows15332]
  all_goals rfl

theorem atot15333 : totK PD2M8K2 D2M8K2.u15333 = [0, 822285969658, 2878128057069, 2827416604136, 651561029885, 23397979727, 0, 0] := by
  rw [show D2M8K2.u15333 = KTree.node D2M8K2.u15329 (nat_lit 33396976) (nat_lit 3417701625) (nat_lit 0) D2M8K2.u15332 from rfl, totK_node, atot15329, atot15332]
  decide +kernel

theorem arows15341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15341 = true := by
  rw [show D2M8K2.u15341 = KTree.node D2M8K2.u15337 (nat_lit 33403978) (nat_lit 3962179576) (nat_lit 0) D2M8K2.u15340 from rfl, allE_node, arows15337, irow15341, arows15340]
  all_goals rfl

theorem atot15341 : totK PD2M8K2 D2M8K2.u15341 = [0, 425933657684, 2353217698149, 3322404250204, 1120753104370, 62016290604, 0, 0] := by
  rw [show D2M8K2.u15341 = KTree.node D2M8K2.u15337 (nat_lit 33403978) (nat_lit 3962179576) (nat_lit 0) D2M8K2.u15340 from rfl, totK_node, atot15337, atot15340]
  decide +kernel

theorem arows15348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15348 = true := by
  rw [show D2M8K2.u15348 = KTree.node D2M8K2.u15344 (nat_lit 33413334) (nat_lit 1745485044) (nat_lit 0) D2M8K2.u15347 from rfl, allE_node, arows15344, irow15348, arows15347]
  all_goals rfl

theorem atot15348 : totK PD2M8K2 D2M8K2.u15348 = [0, 0, 740931745065, 2743627008275, 2896952932666, 806830476695, 42081742489, 0] := by
  rw [show D2M8K2.u15348 = KTree.node D2M8K2.u15344 (nat_lit 33413334) (nat_lit 1745485044) (nat_lit 0) D2M8K2.u15347 from rfl, totK_node, atot15344, atot15347]
  decide +kernel

theorem arows15362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15362 = true := by
  rw [show D2M8K2.u15362 = KTree.node D2M8K2.u15358 (nat_lit 33420478) (nat_lit 3648441214) (nat_lit 0) D2M8K2.u15361 from rfl, allE_node, arows15358, irow15362, arows15361]
  all_goals rfl

theorem atot15362 : totK PD2M8K2 D2M8K2.u15362 = [0, 0, 919168937393, 3174654363816, 2702852916278, 411871882429, 6634014755, 0] := by
  rw [show D2M8K2.u15362 = KTree.node D2M8K2.u15358 (nat_lit 33420478) (nat_lit 3648441214) (nat_lit 0) D2M8K2.u15361 from rfl, totK_node, atot15358, atot15361]
  decide +kernel

theorem arows15369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15369 = true := by
  rw [show D2M8K2.u15369 = KTree.node D2M8K2.u15365 (nat_lit 33428208) (nat_lit 3628317869) (nat_lit 0) D2M8K2.u15368 from rfl, allE_node, arows15365, irow15369, arows15368]
  all_goals rfl

theorem atot15369 : totK PD2M8K2 D2M8K2.u15369 = [0, 754346683581, 2421116710688, 2460508395245, 1302689388969, 304275474298, 9302370699, 0] := by
  rw [show D2M8K2.u15369 = KTree.node D2M8K2.u15365 (nat_lit 33428208) (nat_lit 3628317869) (nat_lit 0) D2M8K2.u15368 from rfl, totK_node, atot15365, atot15368]
  decide +kernel

theorem arows15377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15377 = true := by
  rw [show D2M8K2.u15377 = KTree.node D2M8K2.u15373 (nat_lit 33434935) (nat_lit 1622448289) (nat_lit 0) D2M8K2.u15376 from rfl, allE_node, arows15373, irow15377, arows15376]
  all_goals rfl

theorem atot15377 : totK PD2M8K2 D2M8K2.u15377 = [0, 820565466379, 2791640452423, 2815764105699, 781616261028, 33463823044, 0, 0] := by
  rw [show D2M8K2.u15377 = KTree.node D2M8K2.u15373 (nat_lit 33434935) (nat_lit 1622448289) (nat_lit 0) D2M8K2.u15376 from rfl, totK_node, atot15373, atot15376]
  decide +kernel

theorem arows15384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15384 = true := by
  rw [show D2M8K2.u15384 = KTree.node D2M8K2.u15380 (nat_lit 33445560) (nat_lit 3631534234) (nat_lit 0) D2M8K2.u15383 from rfl, allE_node, arows15380, irow15384, arows15383]
  all_goals rfl

theorem atot15384 : totK PD2M8K2 D2M8K2.u15384 = [0, 418584527484, 2272883300100, 3223051242982, 1179370540646, 101839617370, 1206465782, 0] := by
  rw [show D2M8K2.u15384 = KTree.node D2M8K2.u15380 (nat_lit 33445560) (nat_lit 3631534234) (nat_lit 0) D2M8K2.u15383 from rfl, totK_node, atot15380, atot15383]
  decide +kernel

theorem arows15393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15393 = true := by
  rw [show D2M8K2.u15393 = KTree.node D2M8K2.u15389 (nat_lit 33454694) (nat_lit 4137008514) (nat_lit 0) D2M8K2.u15392 from rfl, allE_node, arows15389, irow15393, arows15392]
  all_goals rfl

theorem atot15393 : totK PD2M8K2 D2M8K2.u15393 = [0, 0, 1051124124340, 3275556901714, 2470644131628, 384377908436, 9467545976, 0] := by
  rw [show D2M8K2.u15393 = KTree.node D2M8K2.u15389 (nat_lit 33454694) (nat_lit 4137008514) (nat_lit 0) D2M8K2.u15392 from rfl, totK_node, atot15389, atot15392]
  decide +kernel

theorem arows15400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15400 = true := by
  rw [show D2M8K2.u15400 = KTree.node D2M8K2.u15396 (nat_lit 33465534) (nat_lit 4045235328) (nat_lit 0) D2M8K2.u15399 from rfl, allE_node, arows15396, irow15400, arows15399]
  all_goals rfl

theorem atot15400 : totK PD2M8K2 D2M8K2.u15400 = [0, 419114938304, 1992696784712, 3115902080615, 1549666743140, 149307412463, 1330264907, 0] := by
  rw [show D2M8K2.u15400 = KTree.node D2M8K2.u15396 (nat_lit 33465534) (nat_lit 4045235328) (nat_lit 0) D2M8K2.u15399 from rfl, totK_node, atot15396, atot15399]
  decide +kernel

theorem arows15408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15408 = true := by
  rw [show D2M8K2.u15408 = KTree.node D2M8K2.u15404 (nat_lit 33474666) (nat_lit 3799323125) (nat_lit 0) D2M8K2.u15407 from rfl, allE_node, arows15404, irow15408, arows15407]
  all_goals rfl

theorem atot15408 : totK PD2M8K2 D2M8K2.u15408 = [0, 773995623353, 2753571328003, 2837350741194, 848068155608, 47263825431, 0, 0] := by
  rw [show D2M8K2.u15408 = KTree.node D2M8K2.u15404 (nat_lit 33474666) (nat_lit 3799323125) (nat_lit 0) D2M8K2.u15407 from rfl, totK_node, atot15404, atot15407]
  decide +kernel

theorem arows15415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15415 = true := by
  rw [show D2M8K2.u15415 = KTree.node D2M8K2.u15411 (nat_lit 33485235) (nat_lit 2430716761) (nat_lit 0) D2M8K2.u15414 from rfl, allE_node, arows15411, irow15415, arows15414]
  all_goals rfl

theorem atot15415 : totK PD2M8K2 D2M8K2.u15415 = [0, 800933205286, 2954955473704, 2889690071031, 605849508634, 16150730369, 0, 0] := by
  rw [show D2M8K2.u15415 = KTree.node D2M8K2.u15411 (nat_lit 33485235) (nat_lit 2430716761) (nat_lit 0) D2M8K2.u15414 from rfl, totK_node, atot15411, atot15414]
  decide +kernel

theorem arows15425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15425 = true := by
  rw [show D2M8K2.u15425 = KTree.node D2M8K2.u15421 (nat_lit 33492938) (nat_lit 3998845473) (nat_lit 0) D2M8K2.u15424 from rfl, allE_node, arows15421, irow15425, arows15424]
  all_goals rfl

theorem atot15425 : totK PD2M8K2 D2M8K2.u15425 = [0, 0, 1189152204865, 3510764872517, 2272504528078, 226615897926, 1239866073, 0] := by
  rw [show D2M8K2.u15425 = KTree.node D2M8K2.u15421 (nat_lit 33492938) (nat_lit 3998845473) (nat_lit 0) D2M8K2.u15424 from rfl, totK_node, atot15421, atot15424]
  decide +kernel

theorem arows15432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15432 = true := by
  rw [show D2M8K2.u15432 = KTree.node D2M8K2.u15428 (nat_lit 33504602) (nat_lit 4039411961) (nat_lit 0) D2M8K2.u15431 from rfl, allE_node, arows15428, irow15432, arows15431]
  all_goals rfl

theorem atot15432 : totK PD2M8K2 D2M8K2.u15432 = [0, 180280610855, 1190380088895, 2998631744891, 2407109444789, 412865482471, 10903467235, 0] := by
  rw [show D2M8K2.u15432 = KTree.node D2M8K2.u15428 (nat_lit 33504602) (nat_lit 4039411961) (nat_lit 0) D2M8K2.u15431 from rfl, totK_node, atot15428, atot15431]
  decide +kernel

theorem arows15440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15440 = true := by
  rw [show D2M8K2.u15440 = KTree.node D2M8K2.u15436 (nat_lit 33516402) (nat_lit 2709049819) (nat_lit 0) D2M8K2.u15439 from rfl, allE_node, arows15436, irow15440, arows15439]
  all_goals rfl

theorem atot15440 : totK PD2M8K2 D2M8K2.u15440 = [0, 718181827073, 2726657102618, 2882045050531, 862283506471, 49487115836, 0, 0] := by
  rw [show D2M8K2.u15440 = KTree.node D2M8K2.u15436 (nat_lit 33516402) (nat_lit 2709049819) (nat_lit 0) D2M8K2.u15439 from rfl, totK_node, atot15436, atot15439]
  decide +kernel

theorem arows15447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15447 = true := by
  rw [show D2M8K2.u15447 = KTree.node D2M8K2.u15443 (nat_lit 33523557) (nat_lit 1495181049) (nat_lit 0) D2M8K2.u15446 from rfl, allE_node, arows15443, irow15447, arows15446]
  all_goals rfl

theorem atot15447 : totK PD2M8K2 D2M8K2.u15447 = [0, 759822092337, 2923333055779, 2892303696509, 672753157926, 37868097037, 0, 0] := by
  rw [show D2M8K2.u15447 = KTree.node D2M8K2.u15443 (nat_lit 33523557) (nat_lit 1495181049) (nat_lit 0) D2M8K2.u15446 from rfl, totK_node, atot15443, atot15446]
  decide +kernel

theorem arows15456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15456 = true := by
  rw [show D2M8K2.u15456 = KTree.node D2M8K2.u15452 (nat_lit 33540613) (nat_lit 1335157693) (nat_lit 0) D2M8K2.u15455 from rfl, allE_node, arows15452, irow15456, arows15455]
  all_goals rfl

theorem atot15456 : totK PD2M8K2 D2M8K2.u15456 = [0, 0, 1488548568437, 3783073148821, 1819423678883, 110265843652, 0, 0] := by
  rw [show D2M8K2.u15456 = KTree.node D2M8K2.u15452 (nat_lit 33540613) (nat_lit 1335157693) (nat_lit 0) D2M8K2.u15455 from rfl, totK_node, atot15452, atot15455]
  decide +kernel

theorem arows15463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15463 = true := by
  rw [show D2M8K2.u15463 = KTree.node D2M8K2.u15459 (nat_lit 33553201) (nat_lit 1506478905) (nat_lit 0) D2M8K2.u15462 from rfl, allE_node, arows15459, irow15463, arows15462]
  all_goals rfl

theorem atot15463 : totK PD2M8K2 D2M8K2.u15463 = [0, 773699682448, 2526734189356, 2649629885341, 1162178864570, 155523942239, 1493059870, 0] := by
  rw [show D2M8K2.u15463 = KTree.node D2M8K2.u15459 (nat_lit 33553201) (nat_lit 1506478905) (nat_lit 0) D2M8K2.u15462 from rfl, totK_node, atot15459, atot15462]
  decide +kernel

theorem arows15471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15471 = true := by
  rw [show D2M8K2.u15471 = KTree.node D2M8K2.u15467 (nat_lit 33559691) (nat_lit 2166252278) (nat_lit 0) D2M8K2.u15470 from rfl, allE_node, arows15467, irow15471, arows15470]
  all_goals rfl

theorem atot15471 : totK PD2M8K2 D2M8K2.u15471 = [0, 829985977163, 2869800894085, 2822145933984, 711462535981, 24967218262, 0, 0] := by
  rw [show D2M8K2.u15471 = KTree.node D2M8K2.u15467 (nat_lit 33559691) (nat_lit 2166252278) (nat_lit 0) D2M8K2.u15470 from rfl, totK_node, atot15467, atot15470]
  decide +kernel

theorem arows15478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15478 = true := by
  rw [show D2M8K2.u15478 = KTree.node D2M8K2.u15474 (nat_lit 33569878) (nat_lit 3542039026) (nat_lit 0) D2M8K2.u15477 from rfl, allE_node, arows15474, irow15478, arows15477]
  all_goals rfl

theorem atot15478 : totK PD2M8K2 D2M8K2.u15478 = [0, 443433827047, 2254489404117, 3296877245347, 1189783140551, 60876470561, 0, 0] := by
  rw [show D2M8K2.u15478 = KTree.node D2M8K2.u15474 (nat_lit 33569878) (nat_lit 3542039026) (nat_lit 0) D2M8K2.u15477 from rfl, totK_node, atot15474, atot15477]
  decide +kernel

theorem arows15489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15489 = true := by
  rw [show D2M8K2.u15489 = KTree.node D2M8K2.u15485 (nat_lit 33578888) (nat_lit 3820606981) (nat_lit 0) D2M8K2.u15488 from rfl, allE_node, arows15485, irow15489, arows15488]
  all_goals rfl

theorem atot15489 : totK PD2M8K2 D2M8K2.u15489 = [0, 0, 1009321390094, 3250573610302, 2595364037604, 371218750229, 6190125969, 0] := by
  rw [show D2M8K2.u15489 = KTree.node D2M8K2.u15485 (nat_lit 33578888) (nat_lit 3820606981) (nat_lit 0) D2M8K2.u15488 from rfl, totK_node, atot15485, atot15488]
  decide +kernel

theorem arows15496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15496 = true := by
  rw [show D2M8K2.u15496 = KTree.node D2M8K2.u15492 (nat_lit 33589508) (nat_lit 3143822982) (nat_lit 0) D2M8K2.u15495 from rfl, allE_node, arows15492, irow15496, arows15495]
  all_goals rfl

theorem atot15496 : totK PD2M8K2 D2M8K2.u15496 = [0, 161564142879, 1017581393005, 2721035693590, 2633035470574, 609201274195, 26682572712, 0] := by
  rw [show D2M8K2.u15496 = KTree.node D2M8K2.u15492 (nat_lit 33589508) (nat_lit 3143822982) (nat_lit 0) D2M8K2.u15495 from rfl, totK_node, atot15492, atot15495]
  decide +kernel

theorem arows15504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15504 = true := by
  rw [show D2M8K2.u15504 = KTree.node D2M8K2.u15500 (nat_lit 33848613) (nat_lit 1400728403) (nat_lit 0) D2M8K2.u15503 from rfl, allE_node, arows15500, irow15504, arows15503]
  all_goals rfl

theorem atot15504 : totK PD2M8K2 D2M8K2.u15504 = [0, 853709498663, 3028644374349, 2759397749837, 513890153708, 14418877666, 0, 0] := by
  rw [show D2M8K2.u15504 = KTree.node D2M8K2.u15500 (nat_lit 33848613) (nat_lit 1400728403) (nat_lit 0) D2M8K2.u15503 from rfl, totK_node, atot15500, atot15503]
  decide +kernel

theorem arows15511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15511 = true := by
  rw [show D2M8K2.u15511 = KTree.node D2M8K2.u15507 (nat_lit 33856129) (nat_lit 1555847182) (nat_lit 0) D2M8K2.u15510 from rfl, allE_node, arows15507, irow15511, arows15510]
  all_goals rfl

theorem atot15511 : totK PD2M8K2 D2M8K2.u15511 = [0, 957490997051, 3136016474850, 2625124857264, 452748379296, 10436162499, 0, 0] := by
  rw [show D2M8K2.u15511 = KTree.node D2M8K2.u15507 (nat_lit 33856129) (nat_lit 1555847182) (nat_lit 0) D2M8K2.u15510 from rfl, totK_node, atot15507, atot15510]
  decide +kernel

theorem arows15520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15520 = true := by
  rw [show D2M8K2.u15520 = KTree.node D2M8K2.u15516 (nat_lit 33863235) (nat_lit 1743532120) (nat_lit 0) D2M8K2.u15519 from rfl, allE_node, arows15516, irow15520, arows15519]
  all_goals rfl

theorem atot15520 : totK PD2M8K2 D2M8K2.u15520 = [0, 0, 1346887853296, 3562354625403, 1943240499911, 189856234876, 1369150432, 0] := by
  rw [show D2M8K2.u15520 = KTree.node D2M8K2.u15516 (nat_lit 33863235) (nat_lit 1743532120) (nat_lit 0) D2M8K2.u15519 from rfl, totK_node, atot15516, atot15519]
  decide +kernel

theorem arows15527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15527 = true := by
  rw [show D2M8K2.u15527 = KTree.node D2M8K2.u15523 (nat_lit 33879219) (nat_lit 2827615864) (nat_lit 0) D2M8K2.u15526 from rfl, allE_node, arows15523, irow15527, arows15526]
  all_goals rfl

theorem atot15527 : totK PD2M8K2 D2M8K2.u15527 = [0, 353535550406, 1967989925111, 3395632177541, 1416619925824, 70260367329, 0, 0] := by
  rw [show D2M8K2.u15527 = KTree.node D2M8K2.u15523 (nat_lit 33879219) (nat_lit 2827615864) (nat_lit 0) D2M8K2.u15526 from rfl, totK_node, atot15523, atot15526]
  decide +kernel

theorem arows15535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15535 = true := by
  rw [show D2M8K2.u15535 = KTree.node D2M8K2.u15531 (nat_lit 33890153) (nat_lit 1815078760) (nat_lit 0) D2M8K2.u15534 from rfl, allE_node, arows15531, irow15535, arows15534]
  all_goals rfl

theorem atot15535 : totK PD2M8K2 D2M8K2.u15535 = [0, 691870872482, 2629743237299, 2981201710681, 925110016143, 50646263903, 0, 0] := by
  rw [show D2M8K2.u15535 = KTree.node D2M8K2.u15531 (nat_lit 33890153) (nat_lit 1815078760) (nat_lit 0) D2M8K2.u15534 from rfl, totK_node, atot15531, atot15534]
  decide +kernel

theorem arows15542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15542 = true := by
  rw [show D2M8K2.u15542 = KTree.node D2M8K2.u15538 (nat_lit 33897601) (nat_lit 1535341690) (nat_lit 0) D2M8K2.u15541 from rfl, allE_node, arows15538, irow15542, arows15541]
  all_goals rfl

theorem atot15542 : totK PD2M8K2 D2M8K2.u15542 = [0, 955687851152, 3207535606197, 2701849492946, 463249328830, 12269110658, 0, 0] := by
  rw [show D2M8K2.u15542 = KTree.node D2M8K2.u15538 (nat_lit 33897601) (nat_lit 1535341690) (nat_lit 0) D2M8K2.u15541 from rfl, totK_node, atot15538, atot15541]
  decide +kernel

theorem arows15552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15552 = true := by
  rw [show D2M8K2.u15552 = KTree.node D2M8K2.u15548 (nat_lit 33908192) (nat_lit 3776120356) (nat_lit 0) D2M8K2.u15551 from rfl, allE_node, arows15548, irow15552, arows15551]
  all_goals rfl

theorem atot15552 : totK PD2M8K2 D2M8K2.u15552 = [0, 0, 1148246798767, 3134586802255, 2354333105311, 592367370747, 33015336044, 0] := by
  rw [show D2M8K2.u15552 = KTree.node D2M8K2.u15548 (nat_lit 33908192) (nat_lit 3776120356) (nat_lit 0) D2M8K2.u15551 from rfl, totK_node, atot15548, atot15551]
  decide +kernel

theorem arows15559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15559 = true := by
  rw [show D2M8K2.u15559 = KTree.node D2M8K2.u15555 (nat_lit 33915059) (nat_lit 2010189207) (nat_lit 0) D2M8K2.u15558 from rfl, allE_node, arows15555, irow15559, arows15558]
  all_goals rfl

theorem atot15559 : totK PD2M8K2 D2M8K2.u15559 = [0, 0, 883405565960, 3188225065929, 2752197908402, 437312731535, 6717450418, 0] := by
  rw [show D2M8K2.u15559 = KTree.node D2M8K2.u15555 (nat_lit 33915059) (nat_lit 2010189207) (nat_lit 0) D2M8K2.u15558 from rfl, totK_node, atot15555, atot15558]
  decide +kernel

theorem arows15567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15567 = true := by
  rw [show D2M8K2.u15567 = KTree.node D2M8K2.u15563 (nat_lit 33923088) (nat_lit 3399852923) (nat_lit 0) D2M8K2.u15566 from rfl, allE_node, arows15563, irow15567, arows15566]
  all_goals rfl

theorem atot15567 : totK PD2M8K2 D2M8K2.u15567 = [0, 413176513979, 1654764973931, 2656517926862, 2065237239047, 412633795889, 10717512769, 0] := by
  rw [show D2M8K2.u15567 = KTree.node D2M8K2.u15563 (nat_lit 33923088) (nat_lit 3399852923) (nat_lit 0) D2M8K2.u15566 from rfl, totK_node, atot15563, atot15566]
  decide +kernel

theorem arows15574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15574 = true := by
  rw [show D2M8K2.u15574 = KTree.node D2M8K2.u15570 (nat_lit 33930060) (nat_lit 2441652066) (nat_lit 0) D2M8K2.u15573 from rfl, allE_node, arows15570, irow15574, arows15573]
  all_goals rfl

theorem atot15574 : totK PD2M8K2 D2M8K2.u15574 = [0, 869423908528, 2946418272206, 2735113086382, 697064036920, 35986755070, 0, 0] := by
  rw [show D2M8K2.u15574 = KTree.node D2M8K2.u15570 (nat_lit 33930060) (nat_lit 2441652066) (nat_lit 0) D2M8K2.u15573 from rfl, totK_node, atot15570, atot15573]
  decide +kernel

theorem arows15583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15583 = true := by
  rw [show D2M8K2.u15583 = KTree.node D2M8K2.u15579 (nat_lit 33939712) (nat_lit 3581029459) (nat_lit 0) D2M8K2.u15582 from rfl, allE_node, arows15579, irow15583, arows15582]
  all_goals rfl

theorem atot15583 : totK PD2M8K2 D2M8K2.u15583 = [0, 824244286439, 2954929466857, 2841791543463, 563117781868, 18030242193, 0, 0] := by
  rw [show D2M8K2.u15583 = KTree.node D2M8K2.u15579 (nat_lit 33939712) (nat_lit 3581029459) (nat_lit 0) D2M8K2.u15582 from rfl, totK_node, atot15579, atot15582]
  decide +kernel

theorem arows15590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15590 = true := by
  rw [show D2M8K2.u15590 = KTree.node D2M8K2.u15586 (nat_lit 33946543) (nat_lit 1857175321) (nat_lit 0) D2M8K2.u15589 from rfl, allE_node, arows15586, irow15590, arows15589]
  all_goals rfl

theorem atot15590 : totK PD2M8K2 D2M8K2.u15590 = [0, 0, 1264429489022, 3564108763052, 2078979514770, 189525328776, 1206465782, 0] := by
  rw [show D2M8K2.u15590 = KTree.node D2M8K2.u15586 (nat_lit 33946543) (nat_lit 1857175321) (nat_lit 0) D2M8K2.u15589 from rfl, totK_node, atot15586, atot15589]
  decide +kernel

theorem arows15598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15598 = true := by
  rw [show D2M8K2.u15598 = KTree.node D2M8K2.u15594 (nat_lit 33958748) (nat_lit 3317573467) (nat_lit 0) D2M8K2.u15597 from rfl, allE_node, arows15594, irow15598, arows15597]
  all_goals rfl

theorem atot15598 : totK PD2M8K2 D2M8K2.u15598 = [0, 0, 894288912138, 3066454860393, 2562385031288, 484096529696, 17590593026, 0] := by
  rw [show D2M8K2.u15598 = KTree.node D2M8K2.u15594 (nat_lit 33958748) (nat_lit 3317573467) (nat_lit 0) D2M8K2.u15597 from rfl, totK_node, atot15594, atot15597]
  decide +kernel

theorem arows15605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15605 = true := by
  rw [show D2M8K2.u15605 = KTree.node D2M8K2.u15601 (nat_lit 34008830) (nat_lit 2538394226) (nat_lit 0) D2M8K2.u15604 from rfl, allE_node, arows15601, irow15605, arows15604]
  all_goals rfl

theorem atot15605 : totK PD2M8K2 D2M8K2.u15605 = [0, 802392591807, 2820073302269, 2771982056888, 797335460075, 54207675616, 0, 0] := by
  rw [show D2M8K2.u15605 = KTree.node D2M8K2.u15601 (nat_lit 34008830) (nat_lit 2538394226) (nat_lit 0) D2M8K2.u15604 from rfl, totK_node, atot15601, atot15604]
  decide +kernel

theorem arows15617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15617 = true := by
  rw [show D2M8K2.u15617 = KTree.node D2M8K2.u15613 (nat_lit 34015875) (nat_lit 1580509495) (nat_lit 0) D2M8K2.u15616 from rfl, allE_node, arows15613, irow15617, arows15616]
  all_goals rfl

theorem atot15617 : totK PD2M8K2 D2M8K2.u15617 = [0, 848977784095, 2958615532559, 2790930778921, 614776789196, 18432639912, 0, 0] := by
  rw [show D2M8K2.u15617 = KTree.node D2M8K2.u15613 (nat_lit 34015875) (nat_lit 1580509495) (nat_lit 0) D2M8K2.u15616 from rfl, totK_node, atot15613, atot15616]
  decide +kernel

theorem arows15624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15624 = true := by
  rw [show D2M8K2.u15624 = KTree.node D2M8K2.u15620 (nat_lit 34030144) (nat_lit 3615292593) (nat_lit 0) D2M8K2.u15623 from rfl, allE_node, arows15620, irow15624, arows15623]
  all_goals rfl

theorem atot15624 : totK PD2M8K2 D2M8K2.u15624 = [0, 0, 1412828804256, 3697825595097, 1877359841866, 145410762084, 1138244013, 0] := by
  rw [show D2M8K2.u15624 = KTree.node D2M8K2.u15620 (nat_lit 34030144) (nat_lit 3615292593) (nat_lit 0) D2M8K2.u15623 from rfl, totK_node, atot15620, atot15623]
  decide +kernel

theorem arows15632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15632 = true := by
  rw [show D2M8K2.u15632 = KTree.node D2M8K2.u15628 (nat_lit 34043924) (nat_lit 3206199631) (nat_lit 0) D2M8K2.u15631 from rfl, allE_node, arows15628, irow15632, arows15631]
  all_goals rfl

theorem atot15632 : totK PD2M8K2 D2M8K2.u15632 = [0, 408214539155, 1903656867571, 3006304799363, 1567742032481, 195481438806, 4977114383, 0] := by
  rw [show D2M8K2.u15632 = KTree.node D2M8K2.u15628 (nat_lit 34043924) (nat_lit 3206199631) (nat_lit 0) D2M8K2.u15631 from rfl, totK_node, atot15628, atot15631]
  decide +kernel

theorem arows15639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15639 = true := by
  rw [show D2M8K2.u15639 = KTree.node D2M8K2.u15635 (nat_lit 34054686) (nat_lit 3951079944) (nat_lit 0) D2M8K2.u15638 from rfl, allE_node, arows15635, irow15639, arows15638]
  all_goals rfl

theorem atot15639 : totK PD2M8K2 D2M8K2.u15639 = [0, 845906720006, 2881348506283, 2789723753645, 749203981599, 37114297496, 0, 0] := by
  rw [show D2M8K2.u15639 = KTree.node D2M8K2.u15635 (nat_lit 34054686) (nat_lit 3951079944) (nat_lit 0) D2M8K2.u15638 from rfl, totK_node, atot15635, atot15638]
  decide +kernel

theorem arows15648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15648 = true := by
  rw [show D2M8K2.u15648 = KTree.node D2M8K2.u15644 (nat_lit 34061602) (nat_lit 4123203255) (nat_lit 0) D2M8K2.u15647 from rfl, allE_node, arows15644, irow15648, arows15647]
  all_goals rfl

theorem atot15648 : totK PD2M8K2 D2M8K2.u15648 = [0, 788562694442, 2901279045703, 2928908533164, 662792720887, 22074302308, 0, 0] := by
  rw [show D2M8K2.u15648 = KTree.node D2M8K2.u15644 (nat_lit 34061602) (nat_lit 4123203255) (nat_lit 0) D2M8K2.u15647 from rfl, totK_node, atot15644, atot15647]
  decide +kernel

theorem arows15655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15655 = true := by
  rw [show D2M8K2.u15655 = KTree.node D2M8K2.u15651 (nat_lit 34071919) (nat_lit 2446349698) (nat_lit 0) D2M8K2.u15654 from rfl, allE_node, arows15651, irow15655, arows15654]
  all_goals rfl

theorem atot15655 : totK PD2M8K2 D2M8K2.u15655 = [0, 0, 1223275843830, 3501503430185, 2252599695927, 221523633676, 1310285577, 0] := by
  rw [show D2M8K2.u15655 = KTree.node D2M8K2.u15651 (nat_lit 34071919) (nat_lit 2446349698) (nat_lit 0) D2M8K2.u15654 from rfl, totK_node, atot15651, atot15654]
  decide +kernel

theorem arows15663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15663 = true := by
  rw [show D2M8K2.u15663 = KTree.node D2M8K2.u15659 (nat_lit 34080654) (nat_lit 3953930835) (nat_lit 0) D2M8K2.u15662 from rfl, allE_node, arows15659, irow15663, arows15662]
  all_goals rfl

theorem atot15663 : totK PD2M8K2 D2M8K2.u15663 = [0, 0, 947497673922, 3180080006701, 2638329726676, 422481334003, 9811245038, 0] := by
  rw [show D2M8K2.u15663 = KTree.node D2M8K2.u15659 (nat_lit 34080654) (nat_lit 3953930835) (nat_lit 0) D2M8K2.u15662 from rfl, totK_node, atot15659, atot15662]
  decide +kernel

theorem arows15670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15670 = true := by
  rw [show D2M8K2.u15670 = KTree.node D2M8K2.u15666 (nat_lit 34091232) (nat_lit 3577290238) (nat_lit 0) D2M8K2.u15669 from rfl, allE_node, arows15666, irow15670, arows15669]
  all_goals rfl

theorem atot15670 : totK PD2M8K2 D2M8K2.u15670 = [0, 0, 799404755768, 2956204239654, 2770827037172, 566511975743, 23120318498, 0] := by
  rw [show D2M8K2.u15670 = KTree.node D2M8K2.u15666 (nat_lit 34091232) (nat_lit 3577290238) (nat_lit 0) D2M8K2.u15669 from rfl, totK_node, atot15666, atot15669]
  decide +kernel

theorem arows15680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15680 = true := by
  rw [show D2M8K2.u15680 = KTree.node D2M8K2.u15676 (nat_lit 34102204) (nat_lit 3510277317) (nat_lit 0) D2M8K2.u15679 from rfl, allE_node, arows15676, irow15680, arows15679]
  all_goals rfl

theorem atot15680 : totK PD2M8K2 D2M8K2.u15680 = [0, 0, 787116215464, 3064513107212, 2849320166966, 412601312334, 7693408802, 0] := by
  rw [show D2M8K2.u15680 = KTree.node D2M8K2.u15676 (nat_lit 34102204) (nat_lit 3510277317) (nat_lit 0) D2M8K2.u15679 from rfl, totK_node, atot15676, atot15679]
  decide +kernel

theorem arows15687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15687 = true := by
  rw [show D2M8K2.u15687 = KTree.node D2M8K2.u15683 (nat_lit 34110624) (nat_lit 3256153750) (nat_lit 0) D2M8K2.u15686 from rfl, allE_node, arows15683, irow15687, arows15686]
  all_goals rfl

theorem atot15687 : totK PD2M8K2 D2M8K2.u15687 = [0, 0, 415031635960, 2041385204308, 3204034933872, 1316716850736, 105741150858, 1275377855] := by
  rw [show D2M8K2.u15687 = KTree.node D2M8K2.u15683 (nat_lit 34110624) (nat_lit 3256153750) (nat_lit 0) D2M8K2.u15686 from rfl, totK_node, atot15683, atot15686]
  decide +kernel

theorem arows15695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15695 = true := by
  rw [show D2M8K2.u15695 = KTree.node D2M8K2.u15691 (nat_lit 34125761) (nat_lit 2206182321) (nat_lit 0) D2M8K2.u15694 from rfl, allE_node, arows15691, irow15695, arows15694]
  all_goals rfl

theorem atot15695 : totK PD2M8K2 D2M8K2.u15695 = [0, 0, 351244263953, 2294044262116, 3470028282848, 994968707975, 34643655712, 0] := by
  rw [show D2M8K2.u15695 = KTree.node D2M8K2.u15691 (nat_lit 34125761) (nat_lit 2206182321) (nat_lit 0) D2M8K2.u15694 from rfl, totK_node, atot15691, atot15694]
  decide +kernel

theorem arows15702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15702 = true := by
  rw [show D2M8K2.u15702 = KTree.node D2M8K2.u15698 (nat_lit 34139684) (nat_lit 3008653717) (nat_lit 0) D2M8K2.u15701 from rfl, allE_node, arows15698, irow15702, arows15701]
  all_goals rfl

theorem atot15702 : totK PD2M8K2 D2M8K2.u15702 = [0, 0, 949269666556, 3090500941775, 2714533243801, 598999161761, 20542502094, 0] := by
  rw [show D2M8K2.u15702 = KTree.node D2M8K2.u15698 (nat_lit 34139684) (nat_lit 3008653717) (nat_lit 0) D2M8K2.u15701 from rfl, totK_node, atot15698, atot15701]
  decide +kernel

theorem arows15711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15711 = true := by
  rw [show D2M8K2.u15711 = KTree.node D2M8K2.u15707 (nat_lit 34150793) (nat_lit 1776290947) (nat_lit 0) D2M8K2.u15710 from rfl, allE_node, arows15707, irow15711, arows15710]
  all_goals rfl

theorem atot15711 : totK PD2M8K2 D2M8K2.u15711 = [0, 0, 1103170937156, 3304067260240, 2413446863200, 413248355150, 13935871499, 0] := by
  rw [show D2M8K2.u15711 = KTree.node D2M8K2.u15707 (nat_lit 34150793) (nat_lit 1776290947) (nat_lit 0) D2M8K2.u15710 from rfl, totK_node, atot15707, atot15710]
  decide +kernel

theorem arows15718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15718 = true := by
  rw [show D2M8K2.u15718 = KTree.node D2M8K2.u15714 (nat_lit 34178860) (nat_lit 3920258384) (nat_lit 0) D2M8K2.u15717 from rfl, allE_node, arows15714, irow15718, arows15717]
  all_goals rfl

theorem atot15718 : totK PD2M8K2 D2M8K2.u15718 = [0, 0, 863844124996, 3065888386316, 2814827985015, 538693619189, 17005153010, 0] := by
  rw [show D2M8K2.u15718 = KTree.node D2M8K2.u15714 (nat_lit 34178860) (nat_lit 3920258384) (nat_lit 0) D2M8K2.u15717 from rfl, totK_node, atot15714, atot15717]
  decide +kernel

theorem arows15726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15726 = true := by
  rw [show D2M8K2.u15726 = KTree.node D2M8K2.u15722 (nat_lit 34189060) (nat_lit 3818132245) (nat_lit 0) D2M8K2.u15725 from rfl, allE_node, arows15722, irow15726, arows15725]
  all_goals rfl

theorem atot15726 : totK PD2M8K2 D2M8K2.u15726 = [0, 0, 816396862079, 2953601994306, 2794860924577, 543308695942, 17972337965, 0] := by
  rw [show D2M8K2.u15726 = KTree.node D2M8K2.u15722 (nat_lit 34189060) (nat_lit 3818132245) (nat_lit 0) D2M8K2.u15725 from rfl, totK_node, atot15722, atot15725]
  decide +kernel

theorem arows15733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15733 = true := by
  rw [show D2M8K2.u15733 = KTree.node D2M8K2.u15729 (nat_lit 34196641) (nat_lit 1499270450) (nat_lit 0) D2M8K2.u15732 from rfl, allE_node, arows15729, irow15733, arows15732]
  all_goals rfl

theorem atot15733 : totK PD2M8K2 D2M8K2.u15733 = [0, 0, 0, 1425331970224, 3673861615717, 1821914841147, 145377448340, 1206465782] := by
  rw [show D2M8K2.u15733 = KTree.node D2M8K2.u15729 (nat_lit 34196641) (nat_lit 1499270450) (nat_lit 0) D2M8K2.u15732 from rfl, totK_node, atot15729, atot15732]
  decide +kernel

theorem arows15744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15744 = true := by
  rw [show D2M8K2.u15744 = KTree.node D2M8K2.u15740 (nat_lit 34211331) (nat_lit 2815332395) (nat_lit 512) D2M8K2.u15743 from rfl, allE_node, arows15740, irow15744, arows15743]
  all_goals rfl

theorem atot15744 : totK PD2M8K2 D2M8K2.u15744 = [0, 0, 394123133746, 1945375640181, 2952318261099, 1525900464544, 215836291516, 5395128787] := by
  rw [show D2M8K2.u15744 = KTree.node D2M8K2.u15740 (nat_lit 34211331) (nat_lit 2815332395) (nat_lit 512) D2M8K2.u15743 from rfl, totK_node, atot15740, atot15743]
  decide +kernel

theorem arows15751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15751 = true := by
  rw [show D2M8K2.u15751 = KTree.node D2M8K2.u15747 (nat_lit 34263943) (nat_lit 2216167742) (nat_lit 0) D2M8K2.u15750 from rfl, allE_node, arows15747, irow15751, arows15750]
  all_goals rfl

theorem atot15751 : totK PD2M8K2 D2M8K2.u15751 = [0, 0, 1155183629221, 3413570750061, 2378228811685, 271137518495, 4626333750, 0] := by
  rw [show D2M8K2.u15751 = KTree.node D2M8K2.u15747 (nat_lit 34263943) (nat_lit 2216167742) (nat_lit 0) D2M8K2.u15750 from rfl, totK_node, atot15747, atot15750]
  decide +kernel

theorem arows15759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15759 = true := by
  rw [show D2M8K2.u15759 = KTree.node D2M8K2.u15755 (nat_lit 34298935) (nat_lit 1871339074) (nat_lit 0) D2M8K2.u15758 from rfl, allE_node, arows15755, irow15759, arows15758]
  all_goals rfl

theorem atot15759 : totK PD2M8K2 D2M8K2.u15759 = [0, 0, 915221774429, 3215681274535, 2704367887791, 377979129626, 6349665391, 0] := by
  rw [show D2M8K2.u15759 = KTree.node D2M8K2.u15755 (nat_lit 34298935) (nat_lit 1871339074) (nat_lit 0) D2M8K2.u15758 from rfl, totK_node, atot15755, atot15758]
  decide +kernel

theorem arows15766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15766 = true := by
  rw [show D2M8K2.u15766 = KTree.node D2M8K2.u15762 (nat_lit 34306063) (nat_lit 1868574391) (nat_lit 0) D2M8K2.u15765 from rfl, allE_node, arows15762, irow15766, arows15765]
  all_goals rfl

theorem atot15766 : totK PD2M8K2 D2M8K2.u15766 = [0, 0, 765562769481, 2884303111425, 2926930372032, 671511846351, 25341380996, 0] := by
  rw [show D2M8K2.u15766 = KTree.node D2M8K2.u15762 (nat_lit 34306063) (nat_lit 1868574391) (nat_lit 0) D2M8K2.u15765 from rfl, totK_node, atot15762, atot15765]
  decide +kernel

theorem arows15775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15775 = true := by
  rw [show D2M8K2.u15775 = KTree.node D2M8K2.u15771 (nat_lit 34317027) (nat_lit 2521059944) (nat_lit 0) D2M8K2.u15774 from rfl, allE_node, arows15771, irow15775, arows15774]
  all_goals rfl

theorem atot15775 : totK PD2M8K2 D2M8K2.u15775 = [0, 433286471789, 1635391582470, 2500886006920, 2076273352884, 546434954483, 26013318776, 0] := by
  rw [show D2M8K2.u15775 = KTree.node D2M8K2.u15771 (nat_lit 34317027) (nat_lit 2521059944) (nat_lit 0) D2M8K2.u15774 from rfl, totK_node, atot15771, atot15774]
  decide +kernel

theorem arows15782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15782 = true := by
  rw [show D2M8K2.u15782 = KTree.node D2M8K2.u15778 (nat_lit 34348987) (nat_lit 1593610323) (nat_lit 0) D2M8K2.u15781 from rfl, allE_node, arows15778, irow15782, arows15781]
  all_goals rfl

theorem atot15782 : totK PD2M8K2 D2M8K2.u15782 = [0, 748556736340, 2911653444403, 2910121429589, 593995623025, 18649515567, 0, 0] := by
  rw [show D2M8K2.u15782 = KTree.node D2M8K2.u15778 (nat_lit 34348987) (nat_lit 1593610323) (nat_lit 0) D2M8K2.u15781 from rfl, totK_node, atot15778, atot15781]
  decide +kernel

theorem arows15790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15790 = true := by
  rw [show D2M8K2.u15790 = KTree.node D2M8K2.u15786 (nat_lit 34356213) (nat_lit 1716804596) (nat_lit 0) D2M8K2.u15789 from rfl, allE_node, arows15786, irow15790, arows15789]
  all_goals rfl

theorem atot15790 : totK PD2M8K2 D2M8K2.u15790 = [0, 794902111556, 2894117113112, 2868630038890, 612939882785, 14919171357, 0, 0] := by
  rw [show D2M8K2.u15790 = KTree.node D2M8K2.u15786 (nat_lit 34356213) (nat_lit 1716804596) (nat_lit 0) D2M8K2.u15789 from rfl, totK_node, atot15786, atot15789]
  decide +kernel

theorem arows15797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15797 = true := by
  rw [show D2M8K2.u15797 = KTree.node D2M8K2.u15793 (nat_lit 34366556) (nat_lit 3073454642) (nat_lit 0) D2M8K2.u15796 from rfl, allE_node, arows15793, irow15797, arows15796]
  all_goals rfl

theorem atot15797 : totK PD2M8K2 D2M8K2.u15797 = [0, 0, 1238338219498, 3534526053225, 2071185596162, 204617869457, 1369150432, 0] := by
  rw [show D2M8K2.u15797 = KTree.node D2M8K2.u15793 (nat_lit 34366556) (nat_lit 3073454642) (nat_lit 0) D2M8K2.u15796 from rfl, totK_node, atot15793, atot15796]
  decide +kernel

theorem arows15807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15807 = true := by
  rw [show D2M8K2.u15807 = KTree.node D2M8K2.u15803 (nat_lit 34378537) (nat_lit 1451707094) (nat_lit 0) D2M8K2.u15806 from rfl, allE_node, arows15803, irow15807, arows15806]
  all_goals rfl

theorem atot15807 : totK PD2M8K2 D2M8K2.u15807 = [0, 442620365002, 2145518130547, 3253213795075, 1322623650227, 75433292096, 0, 0] := by
  rw [show D2M8K2.u15807 = KTree.node D2M8K2.u15803 (nat_lit 34378537) (nat_lit 1451707094) (nat_lit 0) D2M8K2.u15806 from rfl, totK_node, atot15803, atot15806]
  decide +kernel

theorem arows15814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15814 = true := by
  rw [show D2M8K2.u15814 = KTree.node D2M8K2.u15810 (nat_lit 34390493) (nat_lit 2232995411) (nat_lit 0) D2M8K2.u15813 from rfl, allE_node, arows15810, irow15814, arows15813]
  all_goals rfl

theorem atot15814 : totK PD2M8K2 D2M8K2.u15814 = [0, 756797964315, 2791621873900, 2946226776813, 763681863925, 29755051227, 0, 0] := by
  rw [show D2M8K2.u15814 = KTree.node D2M8K2.u15810 (nat_lit 34390493) (nat_lit 2232995411) (nat_lit 0) D2M8K2.u15813 from rfl, totK_node, atot15810, atot15813]
  decide +kernel

theorem arows15822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15822 = true := by
  rw [show D2M8K2.u15822 = KTree.node D2M8K2.u15818 (nat_lit 34397837) (nat_lit 1793506505) (nat_lit 0) D2M8K2.u15821 from rfl, allE_node, arows15818, irow15822, arows15821]
  all_goals rfl

theorem atot15822 : totK PD2M8K2 D2M8K2.u15822 = [0, 801898790771, 2932354069661, 2895083227840, 650529190911, 21610384954, 0, 0] := by
  rw [show D2M8K2.u15822 = KTree.node D2M8K2.u15818 (nat_lit 34397837) (nat_lit 1793506505) (nat_lit 0) D2M8K2.u15821 from rfl, totK_node, atot15818, atot15821]
  decide +kernel

theorem arows15829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15829 = true := by
  rw [show D2M8K2.u15829 = KTree.node D2M8K2.u15825 (nat_lit 34407435) (nat_lit 3644845456) (nat_lit 0) D2M8K2.u15828 from rfl, allE_node, arows15825, irow15829, arows15828]
  all_goals rfl

theorem atot15829 : totK PD2M8K2 D2M8K2.u15829 = [0, 0, 842373469144, 2916658998967, 2813503105331, 710704938065, 34639773963, 0] := by
  rw [show D2M8K2.u15829 = KTree.node D2M8K2.u15825 (nat_lit 34407435) (nat_lit 3644845456) (nat_lit 0) D2M8K2.u15828 from rfl, totK_node, atot15825, atot15828]
  decide +kernel

theorem arows15838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15838 = true := by
  rw [show D2M8K2.u15838 = KTree.node D2M8K2.u15834 (nat_lit 34415233) (nat_lit 1247514891) (nat_lit 0) D2M8K2.u15837 from rfl, allE_node, arows15834, irow15838, arows15837]
  all_goals rfl

theorem atot15838 : totK PD2M8K2 D2M8K2.u15838 = [0, 0, 969927257794, 3189549556693, 2679353580255, 423275685912, 6634014755, 0] := by
  rw [show D2M8K2.u15838 = KTree.node D2M8K2.u15834 (nat_lit 34415233) (nat_lit 1247514891) (nat_lit 0) D2M8K2.u15837 from rfl, totK_node, atot15834, atot15837]
  decide +kernel

theorem arows15845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15845 = true := by
  rw [show D2M8K2.u15845 = KTree.node D2M8K2.u15841 (nat_lit 34464235) (nat_lit 1621334864) (nat_lit 0) D2M8K2.u15844 from rfl, allE_node, arows15841, irow15845, arows15844]
  all_goals rfl

theorem atot15845 : totK PD2M8K2 D2M8K2.u15845 = [0, 664302839380, 2281999338860, 2582660426916, 1367744445623, 294912180910, 9302370699, 0] := by
  rw [show D2M8K2.u15845 = KTree.node D2M8K2.u15841 (nat_lit 34464235) (nat_lit 1621334864) (nat_lit 0) D2M8K2.u15844 from rfl, totK_node, atot15841, atot15844]
  decide +kernel

theorem arows15853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15853 = true := by
  rw [show D2M8K2.u15853 = KTree.node D2M8K2.u15849 (nat_lit 34474065) (nat_lit 1752345397) (nat_lit 0) D2M8K2.u15852 from rfl, allE_node, arows15849, irow15853, arows15852]
  all_goals rfl

theorem atot15853 : totK PD2M8K2 D2M8K2.u15853 = [0, 701567090635, 2646244295145, 2926487662442, 915028836177, 49242870502, 0, 0] := by
  rw [show D2M8K2.u15853 = KTree.node D2M8K2.u15849 (nat_lit 34474065) (nat_lit 1752345397) (nat_lit 0) D2M8K2.u15852 from rfl, totK_node, atot15849, atot15852]
  decide +kernel

theorem arows15860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15860 = true := by
  rw [show D2M8K2.u15860 = KTree.node D2M8K2.u15856 (nat_lit 34480922) (nat_lit 4133817830) (nat_lit 0) D2M8K2.u15859 from rfl, allE_node, arows15856, irow15860, arows15859]
  all_goals rfl

theorem atot15860 : totK PD2M8K2 D2M8K2.u15860 = [0, 741405628350, 2825884814548, 2936561741787, 678284387011, 26994143389, 0, 0] := by
  rw [show D2M8K2.u15860 = KTree.node D2M8K2.u15856 (nat_lit 34480922) (nat_lit 4133817830) (nat_lit 0) D2M8K2.u15859 from rfl, totK_node, atot15856, atot15859]
  decide +kernel

theorem arows15873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15873 = true := by
  rw [show D2M8K2.u15873 = KTree.node D2M8K2.u15869 (nat_lit 34488134) (nat_lit 3978454308) (nat_lit 0) D2M8K2.u15872 from rfl, allE_node, arows15869, irow15873, arows15872]
  all_goals rfl

theorem atot15873 : totK PD2M8K2 D2M8K2.u15873 = [0, 0, 1187092777848, 3524832251200, 2238283474893, 208987758056, 1239866073, 0] := by
  rw [show D2M8K2.u15873 = KTree.node D2M8K2.u15869 (nat_lit 34488134) (nat_lit 3978454308) (nat_lit 0) D2M8K2.u15872 from rfl, totK_node, atot15869, atot15872]
  decide +kernel

theorem arows15880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15880 = true := by
  rw [show D2M8K2.u15880 = KTree.node D2M8K2.u15876 (nat_lit 34499528) (nat_lit 3635493622) (nat_lit 0) D2M8K2.u15879 from rfl, allE_node, arows15876, irow15880, arows15879]
  all_goals rfl

theorem atot15880 : totK PD2M8K2 D2M8K2.u15880 = [0, 89266124844, 944906562880, 2925155366702, 2580264993480, 502717968970, 17826068843, 0] := by
  rw [show D2M8K2.u15880 = KTree.node D2M8K2.u15876 (nat_lit 34499528) (nat_lit 3635493622) (nat_lit 0) D2M8K2.u15879 from rfl, totK_node, atot15876, atot15879]
  decide +kernel

theorem arows15888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15888 = true := by
  rw [show D2M8K2.u15888 = KTree.node D2M8K2.u15884 (nat_lit 34508870) (nat_lit 3956613314) (nat_lit 0) D2M8K2.u15887 from rfl, allE_node, arows15884, irow15888, arows15887]
  all_goals rfl

theorem atot15888 : totK PD2M8K2 D2M8K2.u15888 = [0, 877320349701, 3059710029197, 2743863509502, 553243312364, 16776867537, 0, 0] := by
  rw [show D2M8K2.u15888 = KTree.node D2M8K2.u15884 (nat_lit 34508870) (nat_lit 3956613314) (nat_lit 0) D2M8K2.u15887 from rfl, totK_node, atot15884, atot15887]
  decide +kernel

theorem arows15895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15895 = true := by
  rw [show D2M8K2.u15895 = KTree.node D2M8K2.u15891 (nat_lit 34518859) (nat_lit 1804167824) (nat_lit 0) D2M8K2.u15894 from rfl, allE_node, arows15891, irow15895, arows15894]
  all_goals rfl

theorem atot15895 : totK PD2M8K2 D2M8K2.u15895 = [0, 681193553328, 2803499552174, 3028160474591, 671136083143, 19601020673, 0, 0] := by
  rw [show D2M8K2.u15895 = KTree.node D2M8K2.u15891 (nat_lit 34518859) (nat_lit 1804167824) (nat_lit 0) D2M8K2.u15894 from rfl, totK_node, atot15891, atot15894]
  decide +kernel

theorem arows15904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15904 = true := by
  rw [show D2M8K2.u15904 = KTree.node D2M8K2.u15900 (nat_lit 34530005) (nat_lit 1255321591) (nat_lit 0) D2M8K2.u15903 from rfl, allE_node, arows15900, irow15904, arows15903]
  all_goals rfl

theorem atot15904 : totK PD2M8K2 D2M8K2.u15904 = [0, 0, 1269797849985, 3616824852313, 2070576031683, 168382736802, 1138244013, 0] := by
  rw [show D2M8K2.u15904 = KTree.node D2M8K2.u15900 (nat_lit 34530005) (nat_lit 1255321591) (nat_lit 0) D2M8K2.u15903 from rfl, totK_node, atot15900, atot15903]
  decide +kernel

theorem arows15911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15911 = true := by
  rw [show D2M8K2.u15911 = KTree.node D2M8K2.u15907 (nat_lit 34547170) (nat_lit 4107749676) (nat_lit 0) D2M8K2.u15910 from rfl, allE_node, arows15907, irow15911, arows15910]
  all_goals rfl

theorem atot15911 : totK PD2M8K2 D2M8K2.u15911 = [0, 674155161047, 2375558962547, 2703266349232, 1217274020272, 177065913129, 4977114383, 0] := by
  rw [show D2M8K2.u15911 = KTree.node D2M8K2.u15907 (nat_lit 34547170) (nat_lit 4107749676) (nat_lit 0) D2M8K2.u15910 from rfl, totK_node, atot15907, atot15910]
  decide +kernel

theorem arows15919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15919 = true := by
  rw [show D2M8K2.u15919 = KTree.node D2M8K2.u15915 (nat_lit 34553646) (nat_lit 3636075308) (nat_lit 0) D2M8K2.u15918 from rfl, allE_node, arows15915, irow15919, arows15918]
  all_goals rfl

theorem atot15919 : totK PD2M8K2 D2M8K2.u15919 = [0, 807535186331, 2795049178260, 2843272389488, 832515027189, 43810815329, 0, 0] := by
  rw [show D2M8K2.u15919 = KTree.node D2M8K2.u15915 (nat_lit 34553646) (nat_lit 3636075308) (nat_lit 0) D2M8K2.u15918 from rfl, totK_node, atot15915, atot15918]
  decide +kernel

theorem arows15926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15926 = true := by
  rw [show D2M8K2.u15926 = KTree.node D2M8K2.u15922 (nat_lit 34564300) (nat_lit 3924603948) (nat_lit 0) D2M8K2.u15925 from rfl, allE_node, arows15922, irow15926, arows15925]
  all_goals rfl

theorem atot15926 : totK PD2M8K2 D2M8K2.u15926 = [0, 557448223064, 2519065375527, 3176361557071, 938881181449, 40628634021, 0, 0] := by
  rw [show D2M8K2.u15926 = KTree.node D2M8K2.u15922 (nat_lit 34564300) (nat_lit 3924603948) (nat_lit 0) D2M8K2.u15925 from rfl, totK_node, atot15922, atot15925]
  decide +kernel

theorem arows15936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15936 = true := by
  rw [show D2M8K2.u15936 = KTree.node D2M8K2.u15932 (nat_lit 34571448) (nat_lit 3222553791) (nat_lit 0) D2M8K2.u15935 from rfl, allE_node, arows15932, irow15936, arows15935]
  all_goals rfl

theorem atot15936 : totK PD2M8K2 D2M8K2.u15936 = [0, 0, 1001456443128, 3247053248747, 2599184196239, 354076338705, 6190125969, 0] := by
  rw [show D2M8K2.u15936 = KTree.node D2M8K2.u15932 (nat_lit 34571448) (nat_lit 3222553791) (nat_lit 0) D2M8K2.u15935 from rfl, totK_node, atot15932, atot15935]
  decide +kernel

theorem arows15943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15943 = true := by
  rw [show D2M8K2.u15943 = KTree.node D2M8K2.u15939 (nat_lit 34584196) (nat_lit 3772546580) (nat_lit 0) D2M8K2.u15942 from rfl, allE_node, arows15939, irow15943, arows15942]
  all_goals rfl

theorem atot15943 : totK PD2M8K2 D2M8K2.u15943 = [0, 0, 865937314292, 3042082021109, 2735736225823, 516117005670, 13355831902, 0] := by
  rw [show D2M8K2.u15943 = KTree.node D2M8K2.u15939 (nat_lit 34584196) (nat_lit 3772546580) (nat_lit 0) D2M8K2.u15942 from rfl, totK_node, atot15939, atot15942]
  decide +kernel

theorem arows15951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15951 = true := by
  rw [show D2M8K2.u15951 = KTree.node D2M8K2.u15947 (nat_lit 34590822) (nat_lit 3759520405) (nat_lit 0) D2M8K2.u15950 from rfl, allE_node, arows15947, irow15951, arows15950]
  all_goals rfl

theorem atot15951 : totK PD2M8K2 D2M8K2.u15951 = [0, 0, 950607676358, 3183889431890, 2601412437911, 406606758372, 15860210862, 0] := by
  rw [show D2M8K2.u15951 = KTree.node D2M8K2.u15947 (nat_lit 34590822) (nat_lit 3759520405) (nat_lit 0) D2M8K2.u15950 from rfl, totK_node, atot15947, atot15950]
  decide +kernel

theorem arows15958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15958 = true := by
  rw [show D2M8K2.u15958 = KTree.node D2M8K2.u15954 (nat_lit 34602381) (nat_lit 1476496748) (nat_lit 0) D2M8K2.u15957 from rfl, allE_node, arows15954, irow15958, arows15957]
  all_goals rfl

theorem atot15958 : totK PD2M8K2 D2M8K2.u15958 = [0, 0, 996664590654, 3238589884082, 2566597404990, 354212341025, 6552152644, 0] := by
  rw [show D2M8K2.u15958 = KTree.node D2M8K2.u15954 (nat_lit 34602381) (nat_lit 1476496748) (nat_lit 0) D2M8K2.u15957 from rfl, totK_node, atot15954, atot15957]
  decide +kernel

theorem arows15967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15967 = true := by
  rw [show D2M8K2.u15967 = KTree.node D2M8K2.u15963 (nat_lit 34609907) (nat_lit 2897870831) (nat_lit 0) D2M8K2.u15966 from rfl, allE_node, arows15963, irow15967, arows15966]
  all_goals rfl

theorem atot15967 : totK PD2M8K2 D2M8K2.u15967 = [0, 0, 19692840307, 1534339721395, 3728996785378, 1619787647615, 117065795828, 1310517177] := by
  rw [show D2M8K2.u15967 = KTree.node D2M8K2.u15963 (nat_lit 34609907) (nat_lit 2897870831) (nat_lit 0) D2M8K2.u15966 from rfl, totK_node, atot15963, atot15966]
  decide +kernel

theorem arows15974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15974 = true := by
  rw [show D2M8K2.u15974 = KTree.node D2M8K2.u15970 (nat_lit 34627229) (nat_lit 2278694330) (nat_lit 0) D2M8K2.u15973 from rfl, allE_node, arows15970, irow15974, arows15973]
  all_goals rfl

theorem atot15974 : totK PD2M8K2 D2M8K2.u15974 = [0, 0, 439879725741, 2424157108115, 3329308044675, 989668741284, 39664207724, 0] := by
  rw [show D2M8K2.u15974 = KTree.node D2M8K2.u15970 (nat_lit 34627229) (nat_lit 2278694330) (nat_lit 0) D2M8K2.u15973 from rfl, totK_node, atot15970, atot15973]
  decide +kernel

theorem arows15982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15982 = true := by
  rw [show D2M8K2.u15982 = KTree.node D2M8K2.u15978 (nat_lit 34640975) (nat_lit 2155777725) (nat_lit 0) D2M8K2.u15981 from rfl, allE_node, arows15978, irow15982, arows15981]
  all_goals rfl

theorem atot15982 : totK PD2M8K2 D2M8K2.u15982 = [0, 0, 1232989330295, 3391800800045, 2354462224960, 382273670950, 8493503399, 0] := by
  rw [show D2M8K2.u15982 = KTree.node D2M8K2.u15978 (nat_lit 34640975) (nat_lit 2155777725) (nat_lit 0) D2M8K2.u15981 from rfl, totK_node, atot15978, atot15981]
  decide +kernel

theorem arows15989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15989 = true := by
  rw [show D2M8K2.u15989 = KTree.node D2M8K2.u15985 (nat_lit 34712689) (nat_lit 1507317077) (nat_lit 0) D2M8K2.u15988 from rfl, allE_node, arows15985, irow15989, arows15988]
  all_goals rfl

theorem atot15989 : totK PD2M8K2 D2M8K2.u15989 = [0, 0, 922596662803, 3147479701866, 2704114978673, 460065462993, 14001353513, 0] := by
  rw [show D2M8K2.u15989 = KTree.node D2M8K2.u15985 (nat_lit 34712689) (nat_lit 1507317077) (nat_lit 0) D2M8K2.u15988 from rfl, totK_node, atot15985, atot15988]
  decide +kernel

theorem arows16000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16000 = true := by
  rw [show D2M8K2.u16000 = KTree.node D2M8K2.u15996 (nat_lit 34722998) (nat_lit 3938909156) (nat_lit 0) D2M8K2.u15999 from rfl, allE_node, arows15996, irow16000, arows15999]
  all_goals rfl

theorem atot16000 : totK PD2M8K2 D2M8K2.u16000 = [0, 0, 828909809090, 2923640113290, 2793331264759, 685739075146, 29544568406, 0] := by
  rw [show D2M8K2.u16000 = KTree.node D2M8K2.u15996 (nat_lit 34722998) (nat_lit 3938909156) (nat_lit 0) D2M8K2.u15999 from rfl, totK_node, atot15996, atot15999]
  decide +kernel

theorem arows16007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16007 = true := by
  rw [show D2M8K2.u16007 = KTree.node D2M8K2.u16003 (nat_lit 34730075) (nat_lit 2361985304) (nat_lit 0) D2M8K2.u16006 from rfl, allE_node, arows16003, irow16007, arows16006]
  all_goals rfl

theorem atot16007 : totK PD2M8K2 D2M8K2.u16007 = [0, 0, 653784693692, 2697444982069, 3029134372397, 705960028883, 24598358083, 0] := by
  rw [show D2M8K2.u16007 = KTree.node D2M8K2.u16003 (nat_lit 34730075) (nat_lit 2361985304) (nat_lit 0) D2M8K2.u16006 from rfl, totK_node, atot16003, atot16006]
  decide +kernel

theorem arows16015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16015 = true := by
  rw [show D2M8K2.u16015 = KTree.node D2M8K2.u16011 (nat_lit 34737919) (nat_lit 2402667653) (nat_lit 0) D2M8K2.u16014 from rfl, allE_node, arows16011, irow16015, arows16014]
  all_goals rfl

theorem atot16015 : totK PD2M8K2 D2M8K2.u16015 = [0, 0, 0, 1098769518185, 3357959992985, 2311168225787, 310436620226, 6643327963] := by
  rw [show D2M8K2.u16015 = KTree.node D2M8K2.u16011 (nat_lit 34737919) (nat_lit 2402667653) (nat_lit 0) D2M8K2.u16014 from rfl, totK_node, atot16011, atot16014]
  decide +kernel

theorem arows16022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16022 = true := by
  rw [show D2M8K2.u16022 = KTree.node D2M8K2.u16018 (nat_lit 34754120) (nat_lit 3594943133) (nat_lit 0) D2M8K2.u16021 from rfl, allE_node, arows16018, irow16022, arows16021]
  all_goals rfl

theorem atot16022 : totK PD2M8K2 D2M8K2.u16022 = [0, 0, 649641915702, 2698471911705, 2979473638633, 771959617346, 36365422509, 0] := by
  rw [show D2M8K2.u16022 = KTree.node D2M8K2.u16018 (nat_lit 34754120) (nat_lit 3594943133) (nat_lit 0) D2M8K2.u16021 from rfl, totK_node, atot16018, atot16021]
  decide +kernel

theorem arows16031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16031 = true := by
  rw [show D2M8K2.u16031 = KTree.node D2M8K2.u16027 (nat_lit 34768052) (nat_lit 3673459564) (nat_lit 0) D2M8K2.u16030 from rfl, allE_node, arows16027, irow16031, arows16030]
  all_goals rfl

theorem atot16031 : totK PD2M8K2 D2M8K2.u16031 = [0, 0, 1261992955459, 3527930200178, 2162740042314, 244121235331, 4980514959, 0] := by
  rw [show D2M8K2.u16031 = KTree.node D2M8K2.u16027 (nat_lit 34768052) (nat_lit 3673459564) (nat_lit 0) D2M8K2.u16030 from rfl, totK_node, atot16027, atot16030]
  decide +kernel

theorem arows16038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16038 = true := by
  rw [show D2M8K2.u16038 = KTree.node D2M8K2.u16034 (nat_lit 34799964) (nat_lit 2841629022) (nat_lit 0) D2M8K2.u16037 from rfl, allE_node, arows16034, irow16038, arows16037]
  all_goals rfl

theorem atot16038 : totK PD2M8K2 D2M8K2.u16038 = [0, 0, 893879716115, 3116208392822, 2761918672880, 535004083276, 17663033577, 0] := by
  rw [show D2M8K2.u16038 = KTree.node D2M8K2.u16034 (nat_lit 34799964) (nat_lit 2841629022) (nat_lit 0) D2M8K2.u16037 from rfl, totK_node, atot16034, atot16037]
  decide +kernel

theorem arows16046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16046 = true := by
  rw [show D2M8K2.u16046 = KTree.node D2M8K2.u16042 (nat_lit 34807351) (nat_lit 1884083054) (nat_lit 512) D2M8K2.u16045 from rfl, allE_node, arows16042, irow16046, arows16045]
  all_goals rfl

theorem atot16046 : totK PD2M8K2 D2M8K2.u16046 = [0, 0, 864573993114, 3015251087479, 2804784365860, 533375734205, 14069028002, 0] := by
  rw [show D2M8K2.u16046 = KTree.node D2M8K2.u16042 (nat_lit 34807351) (nat_lit 1884083054) (nat_lit 512) D2M8K2.u16045 from rfl, totK_node, atot16042, atot16045]
  decide +kernel

theorem arows16053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16053 = true := by
  rw [show D2M8K2.u16053 = KTree.node D2M8K2.u16049 (nat_lit 35335707) (nat_lit 3424586560) (nat_lit 0) D2M8K2.u16052 from rfl, allE_node, arows16049, irow16053, arows16052]
  all_goals rfl

theorem atot16053 : totK PD2M8K2 D2M8K2.u16053 = [0, 847096328040, 2587691278518, 2211935048351, 1139920413677, 388735911107, 21982715828, 0] := by
  rw [show D2M8K2.u16053 = KTree.node D2M8K2.u16049 (nat_lit 35335707) (nat_lit 3424586560) (nat_lit 0) D2M8K2.u16052 from rfl, totK_node, atot16049, atot16052]
  decide +kernel

theorem arows16063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16063 = true := by
  rw [show D2M8K2.u16063 = KTree.node D2M8K2.u16059 (nat_lit 35346186) (nat_lit 3566339142) (nat_lit 0) D2M8K2.u16062 from rfl, allE_node, arows16059, irow16063, arows16062]
  all_goals rfl

theorem atot16063 : totK PD2M8K2 D2M8K2.u16063 = [0, 732246126738, 2808357904887, 2920909746043, 655895412802, 18828646126, 0, 0] := by
  rw [show D2M8K2.u16063 = KTree.node D2M8K2.u16059 (nat_lit 35346186) (nat_lit 3566339142) (nat_lit 0) D2M8K2.u16062 from rfl, totK_node, atot16059, atot16062]
  decide +kernel

theorem arows16070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16070 = true := by
  rw [show D2M8K2.u16070 = KTree.node D2M8K2.u16066 (nat_lit 35353921) (nat_lit 1393479757) (nat_lit 0) D2M8K2.u16069 from rfl, allE_node, arows16066, irow16070, arows16069]
  all_goals rfl

theorem atot16070 : totK PD2M8K2 D2M8K2.u16070 = [0, 428339404384, 2155778707029, 3160627749421, 1270390734441, 127248450171, 1369150432, 0] := by
  rw [show D2M8K2.u16070 = KTree.node D2M8K2.u16066 (nat_lit 35353921) (nat_lit 1393479757) (nat_lit 0) D2M8K2.u16069 from rfl, totK_node, atot16066, atot16069]
  decide +kernel

theorem arows16078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16078 = true := by
  rw [show D2M8K2.u16078 = KTree.node D2M8K2.u16074 (nat_lit 35366236) (nat_lit 3030407212) (nat_lit 0) D2M8K2.u16077 from rfl, allE_node, arows16074, irow16078, arows16077]
  all_goals rfl

theorem atot16078 : totK PD2M8K2 D2M8K2.u16078 = [0, 0, 1389128407591, 3740867001433, 1876481587991, 101461403468, 0, 0] := by
  rw [show D2M8K2.u16078 = KTree.node D2M8K2.u16074 (nat_lit 35366236) (nat_lit 3030407212) (nat_lit 0) D2M8K2.u16077 from rfl, totK_node, atot16074, atot16077]
  decide +kernel

theorem arows16085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16085 = true := by
  rw [show D2M8K2.u16085 = KTree.node D2M8K2.u16081 (nat_lit 35381310) (nat_lit 3993979912) (nat_lit 0) D2M8K2.u16084 from rfl, allE_node, arows16081, irow16085, arows16084]
  all_goals rfl

theorem atot16085 : totK PD2M8K2 D2M8K2.u16085 = [0, 858997118062, 2731179858904, 2738528169705, 935085510934, 57847188553, 0, 0] := by
  rw [show D2M8K2.u16085 = KTree.node D2M8K2.u16081 (nat_lit 35381310) (nat_lit 3993979912) (nat_lit 0) D2M8K2.u16084 from rfl, totK_node, atot16081, atot16084]
  decide +kernel

theorem arows16094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16094 = true := by
  rw [show D2M8K2.u16094 = KTree.node D2M8K2.u16090 (nat_lit 35387515) (nat_lit 2231376617) (nat_lit 0) D2M8K2.u16093 from rfl, allE_node, arows16090, irow16094, arows16093]
  all_goals rfl

theorem atot16094 : totK PD2M8K2 D2M8K2.u16094 = [0, 742465857949, 2868434151109, 2959616040187, 673118499497, 23401286164, 0, 0] := by
  rw [show D2M8K2.u16094 = KTree.node D2M8K2.u16090 (nat_lit 35387515) (nat_lit 2231376617) (nat_lit 0) D2M8K2.u16093 from rfl, totK_node, atot16090, atot16093]
  decide +kernel

theorem arows16101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16101 = true := by
  rw [show D2M8K2.u16101 = KTree.node D2M8K2.u16097 (nat_lit 35395046) (nat_lit 4055590085) (nat_lit 0) D2M8K2.u16100 from rfl, allE_node, arows16097, irow16101, arows16100]
  all_goals rfl

theorem atot16101 : totK PD2M8K2 D2M8K2.u16101 = [0, 429727646880, 2263917716822, 3300567818635, 1246508693184, 84253754038, 0, 0] := by
  rw [show D2M8K2.u16101 = KTree.node D2M8K2.u16097 (nat_lit 35395046) (nat_lit 4055590085) (nat_lit 0) D2M8K2.u16100 from rfl, totK_node, atot16097, atot16100]
  decide +kernel

theorem arows16109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16109 = true := by
  rw [show D2M8K2.u16109 = KTree.node D2M8K2.u16105 (nat_lit 35404716) (nat_lit 3412760272) (nat_lit 0) D2M8K2.u16108 from rfl, allE_node, arows16105, irow16109, arows16108]
  all_goals rfl

theorem atot16109 : totK PD2M8K2 D2M8K2.u16109 = [0, 0, 827438782043, 2829441934452, 2801717096272, 734535611852, 33557751070, 0] := by
  rw [show D2M8K2.u16109 = KTree.node D2M8K2.u16105 (nat_lit 35404716) (nat_lit 3412760272) (nat_lit 0) D2M8K2.u16108 from rfl, totK_node, atot16105, atot16108]
  decide +kernel

theorem arows16116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16116 = true := by
  rw [show D2M8K2.u16116 = KTree.node D2M8K2.u16112 (nat_lit 35412601) (nat_lit 1161077428) (nat_lit 0) D2M8K2.u16115 from rfl, allE_node, arows16112, irow16116, arows16115]
  all_goals rfl

theorem atot16116 : totK PD2M8K2 D2M8K2.u16116 = [0, 0, 754240339944, 3083015508043, 2976586229823, 464655996163, 3920116675, 0] := by
  rw [show D2M8K2.u16116 = KTree.node D2M8K2.u16112 (nat_lit 35412601) (nat_lit 1161077428) (nat_lit 0) D2M8K2.u16115 from rfl, totK_node, atot16112, atot16115]
  decide +kernel

theorem arows16128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16128 = true := by
  rw [show D2M8K2.u16128 = KTree.node D2M8K2.u16124 (nat_lit 35420291) (nat_lit 2875366070) (nat_lit 0) D2M8K2.u16127 from rfl, allE_node, arows16124, irow16128, arows16127]
  all_goals rfl

theorem atot16128 : totK PD2M8K2 D2M8K2.u16128 = [0, 825785585047, 2799130736661, 2599391119456, 834876825292, 162140125061, 8063697217, 0] := by
  rw [show D2M8K2.u16128 = KTree.node D2M8K2.u16124 (nat_lit 35420291) (nat_lit 2875366070) (nat_lit 0) D2M8K2.u16127 from rfl, totK_node, atot16124, atot16127]
  decide +kernel

theorem arows16135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16135 = true := by
  rw [show D2M8K2.u16135 = KTree.node D2M8K2.u16131 (nat_lit 35426352) (nat_lit 3542895284) (nat_lit 0) D2M8K2.u16134 from rfl, allE_node, arows16131, irow16135, arows16134]
  all_goals rfl

theorem atot16135 : totK PD2M8K2 D2M8K2.u16135 = [0, 782279399113, 2875107109983, 2897946961751, 655600753626, 22356163970, 0, 0] := by
  rw [show D2M8K2.u16135 = KTree.node D2M8K2.u16131 (nat_lit 35426352) (nat_lit 3542895284) (nat_lit 0) D2M8K2.u16134 from rfl, totK_node, atot16131, atot16134]
  decide +kernel

theorem arows16143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16143 = true := by
  rw [show D2M8K2.u16143 = KTree.node D2M8K2.u16139 (nat_lit 35437594) (nat_lit 4021842791) (nat_lit 0) D2M8K2.u16142 from rfl, allE_node, arows16139, irow16143, arows16142]
  all_goals rfl

theorem atot16143 : totK PD2M8K2 D2M8K2.u16143 = [0, 406574288871, 1980344468483, 3120454506679, 1505717517501, 127769546784, 1206465782, 0] := by
  rw [show D2M8K2.u16143 = KTree.node D2M8K2.u16139 (nat_lit 35437594) (nat_lit 4021842791) (nat_lit 0) D2M8K2.u16142 from rfl, totK_node, atot16139, atot16142]
  decide +kernel

theorem arows16150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16150 = true := by
  rw [show D2M8K2.u16150 = KTree.node D2M8K2.u16146 (nat_lit 35446192) (nat_lit 3366121516) (nat_lit 0) D2M8K2.u16149 from rfl, allE_node, arows16146, irow16150, arows16149]
  all_goals rfl

theorem atot16150 : totK PD2M8K2 D2M8K2.u16150 = [0, 0, 1104814316958, 3355720371468, 2357455865605, 344790887979, 8802081085, 0] := by
  rw [show D2M8K2.u16150 = KTree.node D2M8K2.u16146 (nat_lit 35446192) (nat_lit 3366121516) (nat_lit 0) D2M8K2.u16149 from rfl, totK_node, atot16146, atot16149]
  decide +kernel

theorem arows16159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16159 = true := by
  rw [show D2M8K2.u16159 = KTree.node D2M8K2.u16155 (nat_lit 35459345) (nat_lit 2210272227) (nat_lit 0) D2M8K2.u16158 from rfl, allE_node, arows16155, irow16159, arows16158]
  all_goals rfl

theorem atot16159 : totK PD2M8K2 D2M8K2.u16159 = [0, 636716162045, 2380039306627, 2873640343220, 1196215352341, 108538135395, 1021600638, 0] := by
  rw [show D2M8K2.u16159 = KTree.node D2M8K2.u16155 (nat_lit 35459345) (nat_lit 2210272227) (nat_lit 0) D2M8K2.u16158 from rfl, totK_node, atot16155, atot16158]
  decide +kernel

theorem arows16166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16166 = true := by
  rw [show D2M8K2.u16166 = KTree.node D2M8K2.u16162 (nat_lit 35469275) (nat_lit 2754907509) (nat_lit 0) D2M8K2.u16165 from rfl, allE_node, arows16162, irow16166, arows16165]
  all_goals rfl

theorem atot16166 : totK PD2M8K2 D2M8K2.u16166 = [0, 708752722148, 2655088697184, 2929053625601, 914735182240, 49243144338, 0, 0] := by
  rw [show D2M8K2.u16166 = KTree.node D2M8K2.u16162 (nat_lit 35469275) (nat_lit 2754907509) (nat_lit 0) D2M8K2.u16165 from rfl, totK_node, atot16162, atot16165]
  decide +kernel

theorem arows16174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16174 = true := by
  rw [show D2M8K2.u16174 = KTree.node D2M8K2.u16170 (nat_lit 35476681) (nat_lit 1430994790) (nat_lit 0) D2M8K2.u16173 from rfl, allE_node, arows16170, irow16174, arows16173]
  all_goals rfl

theorem atot16174 : totK PD2M8K2 D2M8K2.u16174 = [0, 673281506373, 2767427789950, 3032549267042, 735684323652, 25657657437, 0, 0] := by
  rw [show D2M8K2.u16174 = KTree.node D2M8K2.u16170 (nat_lit 35476681) (nat_lit 1430994790) (nat_lit 0) D2M8K2.u16173 from rfl, totK_node, atot16170, atot16173]
  decide +kernel

theorem arows16181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16181 = true := by
  rw [show D2M8K2.u16181 = KTree.node D2M8K2.u16177 (nat_lit 35483947) (nat_lit 1805480763) (nat_lit 0) D2M8K2.u16180 from rfl, allE_node, arows16177, irow16181, arows16180]
  all_goals rfl

theorem atot16181 : totK PD2M8K2 D2M8K2.u16181 = [0, 0, 1061636150352, 3382793259446, 2455302958211, 275261251073, 2410950632, 0] := by
  rw [show D2M8K2.u16181 = KTree.node D2M8K2.u16177 (nat_lit 35483947) (nat_lit 1805480763) (nat_lit 0) D2M8K2.u16180 from rfl, totK_node, atot16177, atot16180]
  decide +kernel

theorem arows16191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16191 = true := by
  rw [show D2M8K2.u16191 = KTree.node D2M8K2.u16187 (nat_lit 35496769) (nat_lit 1481225768) (nat_lit 0) D2M8K2.u16190 from rfl, allE_node, arows16187, irow16191, arows16190]
  all_goals rfl

theorem atot16191 : totK PD2M8K2 D2M8K2.u16191 = [0, 393878508058, 1675760088907, 2836037641979, 1927916157530, 295277844819, 8735979960, 0] := by
  rw [show D2M8K2.u16191 = KTree.node D2M8K2.u16187 (nat_lit 35496769) (nat_lit 1481225768) (nat_lit 0) D2M8K2.u16190 from rfl, totK_node, atot16187, atot16190]
  decide +kernel

theorem arows16198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16198 = true := by
  rw [show D2M8K2.u16198 = KTree.node D2M8K2.u16194 (nat_lit 35546605) (nat_lit 1024261028) (nat_lit 0) D2M8K2.u16197 from rfl, allE_node, arows16194, irow16198, arows16197]
  all_goals rfl

theorem atot16198 : totK PD2M8K2 D2M8K2.u16198 = [0, 746020150685, 2809671054748, 2921891644723, 780526448426, 36697364776, 0, 0] := by
  rw [show D2M8K2.u16198 = KTree.node D2M8K2.u16194 (nat_lit 35546605) (nat_lit 1024261028) (nat_lit 0) D2M8K2.u16197 from rfl, totK_node, atot16194, atot16197]
  decide +kernel

theorem arows16206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16206 = true := by
  rw [show D2M8K2.u16206 = KTree.node D2M8K2.u16202 (nat_lit 35553003) (nat_lit 3472770828) (nat_lit 0) D2M8K2.u16205 from rfl, allE_node, arows16202, irow16206, arows16205]
  all_goals rfl

theorem atot16206 : totK PD2M8K2 D2M8K2.u16206 = [0, 810536658978, 2896644446364, 2868088579342, 653298851578, 22547819212, 0, 0] := by
  rw [show D2M8K2.u16206 = KTree.node D2M8K2.u16202 (nat_lit 35553003) (nat_lit 3472770828) (nat_lit 0) D2M8K2.u16205 from rfl, totK_node, atot16202, atot16205]
  decide +kernel

theorem arows16213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16213 = true := by
  rw [show D2M8K2.u16213 = KTree.node D2M8K2.u16209 (nat_lit 35562964) (nat_lit 3765632296) (nat_lit 0) D2M8K2.u16212 from rfl, allE_node, arows16209, irow16213, arows16212]
  all_goals rfl

theorem atot16213 : totK PD2M8K2 D2M8K2.u16213 = [0, 182497872290, 1597353293825, 3329334430330, 1897726155879, 182574640681, 1310285577, 0] := by
  rw [show D2M8K2.u16213 = KTree.node D2M8K2.u16209 (nat_lit 35562964) (nat_lit 3765632296) (nat_lit 0) D2M8K2.u16212 from rfl, totK_node, atot16209, atot16212]
  decide +kernel

theorem arows16222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16222 = true := by
  rw [show D2M8K2.u16222 = KTree.node D2M8K2.u16218 (nat_lit 35571215) (nat_lit 1773255099) (nat_lit 0) D2M8K2.u16221 from rfl, allE_node, arows16218, irow16222, arows16221]
  all_goals rfl

theorem atot16222 : totK PD2M8K2 D2M8K2.u16222 = [0, 0, 1052539137959, 3317066418780, 2474973574074, 335355410540, 5986997553, 0] := by
  rw [show D2M8K2.u16222 = KTree.node D2M8K2.u16218 (nat_lit 35571215) (nat_lit 1773255099) (nat_lit 0) D2M8K2.u16221 from rfl, totK_node, atot16218, atot16221]
  decide +kernel

theorem arows16229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16229 = true := by
  rw [show D2M8K2.u16229 = KTree.node D2M8K2.u16225 (nat_lit 35581857) (nat_lit 968694636) (nat_lit 0) D2M8K2.u16228 from rfl, allE_node, arows16225, irow16229, arows16228]
  all_goals rfl

theorem atot16229 : totK PD2M8K2 D2M8K2.u16229 = [0, 0, 881774656856, 2997398276799, 2658759719036, 594996483230, 26944565983, 0] := by
  rw [show D2M8K2.u16229 = KTree.node D2M8K2.u16225 (nat_lit 35581857) (nat_lit 968694636) (nat_lit 0) D2M8K2.u16228 from rfl, totK_node, atot16225, atot16228]
  decide +kernel

theorem arows16237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16237 = true := by
  rw [show D2M8K2.u16237 = KTree.node D2M8K2.u16233 (nat_lit 35592222) (nat_lit 2399909009) (nat_lit 0) D2M8K2.u16236 from rfl, allE_node, arows16233, irow16237, arows16236]
  all_goals rfl

theorem atot16237 : totK PD2M8K2 D2M8K2.u16237 = [0, 0, 821782504812, 3071844104694, 2866088904315, 434281799884, 6370881270, 0] := by
  rw [show D2M8K2.u16237 = KTree.node D2M8K2.u16233 (nat_lit 35592222) (nat_lit 2399909009) (nat_lit 0) D2M8K2.u16236 from rfl, totK_node, atot16233, atot16236]
  decide +kernel

theorem arows16244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16244 = true := by
  rw [show D2M8K2.u16244 = KTree.node D2M8K2.u16240 (nat_lit 35600678) (nat_lit 4041085370) (nat_lit 0) D2M8K2.u16243 from rfl, allE_node, arows16240, irow16244, arows16243]
  all_goals rfl

theorem atot16244 : totK PD2M8K2 D2M8K2.u16244 = [0, 0, 747160429942, 2869237681187, 2855023049428, 616509376632, 27043760565, 0] := by
  rw [show D2M8K2.u16244 = KTree.node D2M8K2.u16240 (nat_lit 35600678) (nat_lit 4041085370) (nat_lit 0) D2M8K2.u16243 from rfl, totK_node, atot16240, atot16243]
  decide +kernel

theorem arows16255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16255 = true := by
  rw [show D2M8K2.u16255 = KTree.node D2M8K2.u16251 (nat_lit 35611038) (nat_lit 3211442752) (nat_lit 0) D2M8K2.u16254 from rfl, allE_node, arows16251, irow16255, arows16254]
  all_goals rfl

theorem atot16255 : totK PD2M8K2 D2M8K2.u16255 = [0, 0, 0, 1266743041442, 3658561989654, 1890445571318, 158227324493, 1369150432] := by
  rw [show D2M8K2.u16255 = KTree.node D2M8K2.u16251 (nat_lit 35611038) (nat_lit 3211442752) (nat_lit 0) D2M8K2.u16254 from rfl, totK_node, atot16251, atot16254]
  decide +kernel

theorem arows16262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16262 = true := by
  rw [show D2M8K2.u16262 = KTree.node D2M8K2.u16258 (nat_lit 35628532) (nat_lit 4069852912) (nat_lit 0) D2M8K2.u16261 from rfl, allE_node, arows16258, irow16262, arows16261]
  all_goals rfl

theorem atot16262 : totK PD2M8K2 D2M8K2.u16262 = [0, 0, 511088486868, 2321897769548, 3211735062275, 1118892870310, 57409894538, 0] := by
  rw [show D2M8K2.u16262 = KTree.node D2M8K2.u16258 (nat_lit 35628532) (nat_lit 4069852912) (nat_lit 0) D2M8K2.u16261 from rfl, totK_node, atot16258, atot16261]
  decide +kernel

theorem arows16270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16270 = true := by
  rw [show D2M8K2.u16270 = KTree.node D2M8K2.u16266 (nat_lit 35635237) (nat_lit 1128254914) (nat_lit 0) D2M8K2.u16269 from rfl, allE_node, arows16266, irow16270, arows16269]
  all_goals rfl

theorem atot16270 : totK PD2M8K2 D2M8K2.u16270 = [0, 0, 953334060838, 3291229661424, 2673281023535, 416233383280, 8355052609, 0] := by
  rw [show D2M8K2.u16270 = KTree.node D2M8K2.u16266 (nat_lit 35635237) (nat_lit 1128254914) (nat_lit 0) D2M8K2.u16269 from rfl, totK_node, atot16266, atot16269]
  decide +kernel

theorem arows16277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16277 = true := by
  rw [show D2M8K2.u16277 = KTree.node D2M8K2.u16273 (nat_lit 35644400) (nat_lit 3494490830) (nat_lit 0) D2M8K2.u16276 from rfl, allE_node, arows16273, irow16277, arows16276]
  all_goals rfl

theorem atot16277 : totK PD2M8K2 D2M8K2.u16277 = [0, 0, 969346457905, 3142582870616, 2600354415690, 505026122072, 22050969863, 0] := by
  rw [show D2M8K2.u16277 = KTree.node D2M8K2.u16273 (nat_lit 35644400) (nat_lit 3494490830) (nat_lit 0) D2M8K2.u16276 from rfl, totK_node, atot16273, atot16276]
  decide +kernel

theorem arows16286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16286 = true := by
  rw [show D2M8K2.u16286 = KTree.node D2M8K2.u16282 (nat_lit 35672613) (nat_lit 812225814) (nat_lit 512) D2M8K2.u16285 from rfl, allE_node, arows16282, irow16286, arows16285]
  all_goals rfl

theorem atot16286 : totK PD2M8K2 D2M8K2.u16286 = [0, 0, 856454009763, 3016438209566, 2805365369104, 616026906430, 24145857180, 0] := by
  rw [show D2M8K2.u16286 = KTree.node D2M8K2.u16282 (nat_lit 35672613) (nat_lit 812225814) (nat_lit 512) D2M8K2.u16285 from rfl, totK_node, atot16282, atot16285]
  decide +kernel

theorem arows16293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16293 = true := by
  rw [show D2M8K2.u16293 = KTree.node D2M8K2.u16289 (nat_lit 35683775) (nat_lit 2116340185) (nat_lit 0) D2M8K2.u16292 from rfl, allE_node, arows16289, irow16293, arows16292]
  all_goals rfl

theorem atot16293 : totK PD2M8K2 D2M8K2.u16293 = [0, 0, 749483200495, 2817461075118, 2905677261551, 680449721398, 25390212686, 0] := by
  rw [show D2M8K2.u16293 = KTree.node D2M8K2.u16289 (nat_lit 35683775) (nat_lit 2116340185) (nat_lit 0) D2M8K2.u16292 from rfl, totK_node, atot16289, atot16292]
  decide +kernel

theorem arows16301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16301 = true := by
  rw [show D2M8K2.u16301 = KTree.node D2M8K2.u16297 (nat_lit 35691590) (nat_lit 4151327674) (nat_lit 0) D2M8K2.u16300 from rfl, allE_node, arows16297, irow16301, arows16300]
  all_goals rfl

theorem atot16301 : totK PD2M8K2 D2M8K2.u16301 = [0, 0, 0, 1117506646091, 3383477895277, 2204907304541, 279047417188, 6301476269] := by
  rw [show D2M8K2.u16301 = KTree.node D2M8K2.u16297 (nat_lit 35691590) (nat_lit 4151327674) (nat_lit 0) D2M8K2.u16300 from rfl, totK_node, atot16297, atot16300]
  decide +kernel

theorem arows16308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16308 = true := by
  rw [show D2M8K2.u16308 = KTree.node D2M8K2.u16304 (nat_lit 35708024) (nat_lit 3414893343) (nat_lit 0) D2M8K2.u16307 from rfl, allE_node, arows16304, irow16308, arows16307]
  all_goals rfl

theorem atot16308 : totK PD2M8K2 D2M8K2.u16308 = [0, 0, 602869134900, 2624447850132, 3062377708515, 834657375642, 43054641264, 0] := by
  rw [show D2M8K2.u16308 = KTree.node D2M8K2.u16304 (nat_lit 35708024) (nat_lit 3414893343) (nat_lit 0) D2M8K2.u16307 from rfl, totK_node, atot16304, atot16307]
  decide +kernel

theorem arows16318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16318 = true := by
  rw [show D2M8K2.u16318 = KTree.node D2M8K2.u16314 (nat_lit 35718657) (nat_lit 1817600003) (nat_lit 0) D2M8K2.u16317 from rfl, allE_node, arows16314, irow16318, arows16317]
  all_goals rfl

theorem atot16318 : totK PD2M8K2 D2M8K2.u16318 = [0, 0, 823335840090, 2964966409820, 2811251047087, 658978094006, 25193340015, 0] := by
  rw [show D2M8K2.u16318 = KTree.node D2M8K2.u16314 (nat_lit 35718657) (nat_lit 1817600003) (nat_lit 0) D2M8K2.u16317 from rfl, totK_node, atot16314, atot16317]
  decide +kernel

theorem arows16325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16325 = true := by
  rw [show D2M8K2.u16325 = KTree.node D2M8K2.u16321 (nat_lit 35726376) (nat_lit 3442028263) (nat_lit 0) D2M8K2.u16324 from rfl, allE_node, arows16321, irow16325, arows16324]
  all_goals rfl

theorem atot16325 : totK PD2M8K2 D2M8K2.u16325 = [0, 0, 586757166690, 2575782971521, 3123247629705, 822684706502, 32038556994, 0] := by
  rw [show D2M8K2.u16325 = KTree.node D2M8K2.u16321 (nat_lit 35726376) (nat_lit 3442028263) (nat_lit 0) D2M8K2.u16324 from rfl, totK_node, atot16321, atot16324]
  decide +kernel

theorem arows16333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16333 = true := by
  rw [show D2M8K2.u16333 = KTree.node D2M8K2.u16329 (nat_lit 35739394) (nat_lit 3982757639) (nat_lit 0) D2M8K2.u16332 from rfl, allE_node, arows16329, irow16333, arows16332]
  all_goals rfl

theorem atot16333 : totK PD2M8K2 D2M8K2.u16333 = [0, 0, 0, 1233330605111, 3344097263459, 2163008827512, 284125064381, 6363931553] := by
  rw [show D2M8K2.u16333 = KTree.node D2M8K2.u16329 (nat_lit 35739394) (nat_lit 3982757639) (nat_lit 0) D2M8K2.u16332 from rfl, totK_node, atot16329, atot16332]
  decide +kernel

theorem arows16340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16340 = true := by
  rw [show D2M8K2.u16340 = KTree.node D2M8K2.u16336 (nat_lit 35791929) (nat_lit 1161352449) (nat_lit 0) D2M8K2.u16339 from rfl, allE_node, arows16336, irow16340, arows16339]
  all_goals rfl

theorem atot16340 : totK PD2M8K2 D2M8K2.u16340 = [0, 0, 843057015360, 2906790925898, 2753557683663, 695385500005, 35337597914, 0] := by
  rw [show D2M8K2.u16340 = KTree.node D2M8K2.u16336 (nat_lit 35791929) (nat_lit 1161352449) (nat_lit 0) D2M8K2.u16339 from rfl, totK_node, atot16336, atot16339]
  decide +kernel

theorem arows16349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16349 = true := by
  rw [show D2M8K2.u16349 = KTree.node D2M8K2.u16345 (nat_lit 35798813) (nat_lit 2298722737) (nat_lit 0) D2M8K2.u16348 from rfl, allE_node, arows16345, irow16349, arows16348]
  all_goals rfl

theorem atot16349 : totK PD2M8K2 D2M8K2.u16349 = [0, 0, 814717611162, 2819591920541, 2804532080148, 732121276762, 33775214585, 0] := by
  rw [show D2M8K2.u16349 = KTree.node D2M8K2.u16345 (nat_lit 35798813) (nat_lit 2298722737) (nat_lit 0) D2M8K2.u16348 from rfl, totK_node, atot16345, atot16348]
  decide +kernel

theorem arows16356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16356 = true := by
  rw [show D2M8K2.u16356 = KTree.node D2M8K2.u16352 (nat_lit 35808746) (nat_lit 4013508817) (nat_lit 0) D2M8K2.u16355 from rfl, allE_node, arows16352, irow16356, arows16355]
  all_goals rfl

theorem atot16356 : totK PD2M8K2 D2M8K2.u16356 = [0, 0, 471189508466, 2410664934269, 3277961765091, 974446230366, 39946649489, 0] := by
  rw [show D2M8K2.u16356 = KTree.node D2M8K2.u16352 (nat_lit 35808746) (nat_lit 4013508817) (nat_lit 0) D2M8K2.u16355 from rfl, totK_node, atot16352, atot16355]
  decide +kernel

theorem arows16364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16364 = true := by
  rw [show D2M8K2.u16364 = KTree.node D2M8K2.u16360 (nat_lit 35816091) (nat_lit 3668430525) (nat_lit 0) D2M8K2.u16363 from rfl, allE_node, arows16360, irow16364, arows16363]
  all_goals rfl

theorem atot16364 : totK PD2M8K2 D2M8K2.u16364 = [0, 0, 0, 1020617855218, 3248849066226, 2431384449756, 333573009512, 6075545519] := by
  rw [show D2M8K2.u16364 = KTree.node D2M8K2.u16360 (nat_lit 35816091) (nat_lit 3668430525) (nat_lit 0) D2M8K2.u16363 from rfl, totK_node, atot16360, atot16363]
  decide +kernel

theorem arows16371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16371 = true := by
  rw [show D2M8K2.u16371 = KTree.node D2M8K2.u16367 (nat_lit 35828680) (nat_lit 3851490194) (nat_lit 0) D2M8K2.u16370 from rfl, allE_node, arows16367, irow16371, arows16370]
  all_goals rfl

theorem atot16371 : totK PD2M8K2 D2M8K2.u16371 = [0, 0, 0, 822566303585, 2929875171006, 2663484080806, 598556824010, 26589411484] := by
  rw [show D2M8K2.u16371 = KTree.node D2M8K2.u16367 (nat_lit 35828680) (nat_lit 3851490194) (nat_lit 0) D2M8K2.u16370 from rfl, totK_node, atot16367, atot16370]
  decide +kernel

theorem arows14 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14 = true := by
  rw [show D2M8K2.u14 = KTree.node D2M8K2.u6 (nat_lit 10373) (nat_lit 2241786272) (nat_lit 0) D2M8K2.u13 from rfl, allE_node, arows6, irow14, arows13]
  all_goals rfl

theorem atot14 : totK PD2M8K2 D2M8K2.u14 = [1702803593939, 6033588440996, 5587800986092, 1072160103435, 29835480879, 0, 0, 0] := by
  rw [show D2M8K2.u14 = KTree.node D2M8K2.u6 (nat_lit 10373) (nat_lit 2241786272) (nat_lit 0) D2M8K2.u13 from rfl, totK_node, atot6, atot13]
  decide +kernel

theorem arows29 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u29 = true := by
  rw [show D2M8K2.u29 = KTree.node D2M8K2.u21 (nat_lit 23910) (nat_lit 3673690346) (nat_lit 0) D2M8K2.u28 from rfl, allE_node, arows21, irow29, arows28]
  all_goals rfl

theorem atot29 : totK PD2M8K2 D2M8K2.u29 = [422999544115, 3427489089363, 6828807396027, 3326777613703, 274434250596, 1369150432, 0, 0] := by
  rw [show D2M8K2.u29 = KTree.node D2M8K2.u21 (nat_lit 23910) (nat_lit 3673690346) (nat_lit 0) D2M8K2.u28 from rfl, totK_node, atot21, atot28]
  decide +kernel

theorem arows45 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u45 = true := by
  rw [show D2M8K2.u45 = KTree.node D2M8K2.u37 (nat_lit 89424) (nat_lit 3395389472) (nat_lit 0) D2M8K2.u44 from rfl, allE_node, arows37, irow45, arows44]
  all_goals rfl

theorem atot45 : totK PD2M8K2 D2M8K2.u45 = [1598824971763, 5700720082875, 5641056079365, 1434583572892, 67546080473, 0, 0, 0] := by
  rw [show D2M8K2.u45 = KTree.node D2M8K2.u37 (nat_lit 89424) (nat_lit 3395389472) (nat_lit 0) D2M8K2.u44 from rfl, totK_node, atot37, atot44]
  decide +kernel

theorem arows60 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u60 = true := by
  rw [show D2M8K2.u60 = KTree.node D2M8K2.u52 (nat_lit 106283) (nat_lit 2647430059) (nat_lit 0) D2M8K2.u59 from rfl, allE_node, arows52, irow60, arows59]
  all_goals rfl

theorem atot60 : totK PD2M8K2 D2M8K2.u60 = [414661219762, 3100293299117, 6422880819150, 3808877573310, 514587350713, 14222663156, 0, 0] := by
  rw [show D2M8K2.u60 = KTree.node D2M8K2.u52 (nat_lit 106283) (nat_lit 2647430059) (nat_lit 0) D2M8K2.u59 from rfl, totK_node, atot52, atot59]
  decide +kernel

theorem arows77 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u77 = true := by
  rw [show D2M8K2.u77 = KTree.node D2M8K2.u69 (nat_lit 127585) (nat_lit 1562614071) (nat_lit 0) D2M8K2.u76 from rfl, allE_node, arows69, irow77, arows76]
  all_goals rfl

theorem atot77 : totK PD2M8K2 D2M8K2.u77 = [1189966585591, 4727359127810, 5832067510005, 2374824635068, 245453876638, 4574395652, 0, 0] := by
  rw [show D2M8K2.u77 = KTree.node D2M8K2.u69 (nat_lit 127585) (nat_lit 1562614071) (nat_lit 0) D2M8K2.u76 from rfl, totK_node, atot69, atot76]
  decide +kernel

theorem arows92 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u92 = true := by
  rw [show D2M8K2.u92 = KTree.node D2M8K2.u84 (nat_lit 144929) (nat_lit 2033653000) (nat_lit 0) D2M8K2.u91 from rfl, allE_node, arows84, irow92, arows91]
  all_goals rfl

theorem atot92 : totK PD2M8K2 D2M8K2.u92 = [824002103115, 4166391897152, 6362236443409, 2796122713377, 225632254429, 1239866073, 0, 0] := by
  rw [show D2M8K2.u92 = KTree.node D2M8K2.u84 (nat_lit 144929) (nat_lit 2033653000) (nat_lit 0) D2M8K2.u91 from rfl, totK_node, atot84, atot91]
  decide +kernel

theorem arows108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u108 = true := by
  rw [show D2M8K2.u108 = KTree.node D2M8K2.u100 (nat_lit 165937) (nat_lit 1519155515) (nat_lit 0) D2M8K2.u107 from rfl, allE_node, arows100, irow108, arows107]
  all_goals rfl

theorem atot108 : totK PD2M8K2 D2M8K2.u108 = [911709218912, 3834573334332, 5654117430402, 3316001661496, 541041634867, 17826068843, 0, 0] := by
  rw [show D2M8K2.u108 = KTree.node D2M8K2.u100 (nat_lit 165937) (nat_lit 1519155515) (nat_lit 0) D2M8K2.u107 from rfl, totK_node, atot100, atot107]
  decide +kernel

theorem arows123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u123 = true := by
  rw [show D2M8K2.u123 = KTree.node D2M8K2.u115 (nat_lit 180078) (nat_lit 4018426320) (nat_lit 0) D2M8K2.u122 from rfl, allE_node, arows115, irow123, arows122]
  all_goals rfl

theorem atot123 : totK PD2M8K2 D2M8K2.u123 = [1096639206293, 4753475947891, 6111016520437, 2177022610499, 167208824152, 1138244013, 0, 0] := by
  rw [show D2M8K2.u123 = KTree.node D2M8K2.u115 (nat_lit 180078) (nat_lit 4018426320) (nat_lit 0) D2M8K2.u122 from rfl, totK_node, atot115, atot122]
  decide +kernel

theorem arows141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u141 = true := by
  rw [show D2M8K2.u141 = KTree.node D2M8K2.u133 (nat_lit 202539) (nat_lit 3511077627) (nat_lit 0) D2M8K2.u140 from rfl, allE_node, arows133, irow141, arows140]
  all_goals rfl

theorem atot141 : totK PD2M8K2 D2M8K2.u141 = [752182103749, 3943100899743, 6320870937837, 3001100296008, 318530341955, 4977114383, 0, 0] := by
  rw [show D2M8K2.u141 = KTree.node D2M8K2.u133 (nat_lit 202539) (nat_lit 3511077627) (nat_lit 0) D2M8K2.u140 from rfl, totK_node, atot133, atot140]
  decide +kernel

theorem arows156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u156 = true := by
  rw [show D2M8K2.u156 = KTree.node D2M8K2.u148 (nat_lit 220584) (nat_lit 3263067135) (nat_lit 0) D2M8K2.u155 from rfl, allE_node, arows148, irow156, arows155]
  all_goals rfl

theorem atot156 : totK PD2M8K2 D2M8K2.u156 = [1267087244509, 5020827324229, 5967141208260, 2012242633285, 145170564011, 1310285577, 0, 0] := by
  rw [show D2M8K2.u156 = KTree.node D2M8K2.u148 (nat_lit 220584) (nat_lit 3263067135) (nat_lit 0) D2M8K2.u155 from rfl, totK_node, atot148, atot155]
  decide +kernel

theorem arows172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u172 = true := by
  rw [show D2M8K2.u172 = KTree.node D2M8K2.u164 (nat_lit 239660) (nat_lit 3656716505) (nat_lit 0) D2M8K2.u171 from rfl, allE_node, arows164, irow172, arows171]
  all_goals rfl

theorem atot172 : totK PD2M8K2 D2M8K2.u172 = [0, 1857356548121, 6208805524433, 5290348379010, 943022081564, 31562413104, 0, 0] := by
  rw [show D2M8K2.u172 = KTree.node D2M8K2.u164 (nat_lit 239660) (nat_lit 3656716505) (nat_lit 0) D2M8K2.u171 from rfl, totK_node, atot164, atot171]
  decide +kernel

theorem arows187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u187 = true := by
  rw [show D2M8K2.u187 = KTree.node D2M8K2.u179 (nat_lit 260352) (nat_lit 3686612343) (nat_lit 0) D2M8K2.u186 from rfl, allE_node, arows179, irow187, arows186]
  all_goals rfl

theorem atot187 : totK PD2M8K2 D2M8K2.u187 = [0, 1702154684176, 6019906277934, 5551189166085, 989367352279, 32287719781, 0, 0] := by
  rw [show D2M8K2.u187 = KTree.node D2M8K2.u179 (nat_lit 260352) (nat_lit 3686612343) (nat_lit 0) D2M8K2.u186 from rfl, totK_node, atot179, atot186]
  decide +kernel

theorem arows204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u204 = true := by
  rw [show D2M8K2.u204 = KTree.node D2M8K2.u196 (nat_lit 277722) (nat_lit 3393476042) (nat_lit 0) D2M8K2.u203 from rfl, allE_node, arows196, irow204, arows203]
  all_goals rfl

theorem atot204 : totK PD2M8K2 D2M8K2.u204 = [0, 393870398829, 3502859374861, 6881147723797, 3041436411620, 274894992886, 1369150432, 0] := by
  rw [show D2M8K2.u204 = KTree.node D2M8K2.u196 (nat_lit 277722) (nat_lit 3393476042) (nat_lit 0) D2M8K2.u203 from rfl, totK_node, atot196, atot203]
  decide +kernel

theorem arows219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u219 = true := by
  rw [show D2M8K2.u219 = KTree.node D2M8K2.u211 (nat_lit 340333) (nat_lit 1054169322) (nat_lit 0) D2M8K2.u218 from rfl, allE_node, arows211, irow219, arows218]
  all_goals rfl

theorem atot219 : totK PD2M8K2 D2M8K2.u219 = [0, 1757917029991, 6110744676052, 5525232955143, 987983023214, 24620496078, 0, 0] := by
  rw [show D2M8K2.u219 = KTree.node D2M8K2.u211 (nat_lit 340333) (nat_lit 1054169322) (nat_lit 0) D2M8K2.u218 from rfl, totK_node, atot211, atot218]
  decide +kernel

theorem arows235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u235 = true := by
  rw [show D2M8K2.u235 = KTree.node D2M8K2.u227 (nat_lit 379474) (nat_lit 3754494459) (nat_lit 0) D2M8K2.u234 from rfl, allE_node, arows227, irow235, arows234]
  all_goals rfl

theorem atot235 : totK PD2M8K2 D2M8K2.u235 = [0, 1594489393452, 5858902146393, 5729568284758, 1173066289560, 34669441363, 0, 0] := by
  rw [show D2M8K2.u235 = KTree.node D2M8K2.u227 (nat_lit 379474) (nat_lit 3754494459) (nat_lit 0) D2M8K2.u234 from rfl, totK_node, atot227, atot234]
  decide +kernel

theorem arows250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u250 = true := by
  rw [show D2M8K2.u250 = KTree.node D2M8K2.u242 (nat_lit 417317) (nat_lit 1992032299) (nat_lit 0) D2M8K2.u249 from rfl, allE_node, arows242, irow250, arows249]
  all_goals rfl

theorem atot250 : totK PD2M8K2 D2M8K2.u250 = [0, 1653787452067, 5928686289490, 5639840692649, 1098063821170, 33298006632, 0, 0] := by
  rw [show D2M8K2.u250 = KTree.node D2M8K2.u242 (nat_lit 417317) (nat_lit 1992032299) (nat_lit 0) D2M8K2.u249 from rfl, totK_node, atot242, atot249]
  decide +kernel

theorem arows269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u269 = true := by
  rw [show D2M8K2.u269 = KTree.node D2M8K2.u261 (nat_lit 456315) (nat_lit 2930925368) (nat_lit 0) D2M8K2.u268 from rfl, allE_node, arows261, irow269, arows268]
  all_goals rfl

theorem atot269 : totK PD2M8K2 D2M8K2.u269 = [0, 1734914274910, 6035671297478, 5556044002257, 1064673863794, 29109610414, 0, 0] := by
  rw [show D2M8K2.u269 = KTree.node D2M8K2.u261 (nat_lit 456315) (nat_lit 2930925368) (nat_lit 0) D2M8K2.u268 from rfl, totK_node, atot261, atot268]
  decide +kernel

theorem arows284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u284 = true := by
  rw [show D2M8K2.u284 = KTree.node D2M8K2.u276 (nat_lit 474262) (nat_lit 2988145152) (nat_lit 0) D2M8K2.u283 from rfl, allE_node, arows276, irow284, arows283]
  all_goals rfl

theorem atot284 : totK PD2M8K2 D2M8K2.u284 = [637203700550, 3051758590615, 5521359304513, 4318688921097, 916536171642, 32229130377, 0, 0] := by
  rw [show D2M8K2.u284 = KTree.node D2M8K2.u276 (nat_lit 474262) (nat_lit 2988145152) (nat_lit 0) D2M8K2.u283 from rfl, totK_node, atot276, atot283]
  decide +kernel

theorem arows300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u300 = true := by
  rw [show D2M8K2.u300 = KTree.node D2M8K2.u292 (nat_lit 1010046) (nat_lit 3811219124) (nat_lit 0) D2M8K2.u299 from rfl, allE_node, arows292, irow300, arows299]
  all_goals rfl

theorem atot300 : totK PD2M8K2 D2M8K2.u300 = [1388349800382, 5440802990856, 5919371314030, 1526849860317, 62940620160, 0, 0, 0] := by
  rw [show D2M8K2.u300 = KTree.node D2M8K2.u292 (nat_lit 1010046) (nat_lit 3811219124) (nat_lit 0) D2M8K2.u299 from rfl, totK_node, atot292, atot299]
  decide +kernel

theorem arows315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u315 = true := by
  rw [show D2M8K2.u315 = KTree.node D2M8K2.u307 (nat_lit 1030797) (nat_lit 1476496748) (nat_lit 0) D2M8K2.u314 from rfl, allE_node, arows307, irow315, arows314]
  all_goals rfl

theorem atot315 : totK PD2M8K2 D2M8K2.u315 = [501585544218, 3395525910069, 6694506671308, 3459494630232, 294744850255, 1369150432, 0, 0] := by
  rw [show D2M8K2.u315 = KTree.node D2M8K2.u307 (nat_lit 1030797) (nat_lit 1476496748) (nat_lit 0) D2M8K2.u314 from rfl, totK_node, atot307, atot314]
  decide +kernel

theorem arows332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u332 = true := by
  rw [show D2M8K2.u332 = KTree.node D2M8K2.u324 (nat_lit 1054274) (nat_lit 3266331838) (nat_lit 0) D2M8K2.u331 from rfl, allE_node, arows324, irow332, arows331]
  all_goals rfl

theorem atot332 : totK PD2M8K2 D2M8K2.u332 = [1160968686033, 4719423581590, 5749812411882, 2382920407961, 451916893920, 29044448997, 0, 0] := by
  rw [show D2M8K2.u332 = KTree.node D2M8K2.u324 (nat_lit 1054274) (nat_lit 3266331838) (nat_lit 0) D2M8K2.u331 from rfl, totK_node, atot324, atot331]
  decide +kernel

theorem arows347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u347 = true := by
  rw [show D2M8K2.u347 = KTree.node D2M8K2.u339 (nat_lit 1074388) (nat_lit 3254823481) (nat_lit 0) D2M8K2.u346 from rfl, allE_node, arows339, irow347, arows346]
  all_goals rfl

theorem atot347 : totK PD2M8K2 D2M8K2.u347 = [493992587577, 2823742149481, 5708969091921, 4448449376684, 905859835054, 23754806261, 0, 0] := by
  rw [show D2M8K2.u347 = KTree.node D2M8K2.u339 (nat_lit 1074388) (nat_lit 3254823481) (nat_lit 0) D2M8K2.u346 from rfl, totK_node, atot339, atot346]
  decide +kernel

theorem arows363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u363 = true := by
  rw [show D2M8K2.u363 = KTree.node D2M8K2.u355 (nat_lit 1088114) (nat_lit 4011908747) (nat_lit 0) D2M8K2.u362 from rfl, allE_node, arows355, irow363, arows362]
  all_goals rfl

theorem atot363 : totK PD2M8K2 D2M8K2.u363 = [1613103918421, 5731704911908, 5647143428849, 1383176484862, 57471429349, 0, 0, 0] := by
  rw [show D2M8K2.u363 = KTree.node D2M8K2.u355 (nat_lit 1088114) (nat_lit 4011908747) (nat_lit 0) D2M8K2.u362 from rfl, totK_node, atot355, atot362]
  decide +kernel

theorem arows378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u378 = true := by
  rw [show D2M8K2.u378 = KTree.node D2M8K2.u370 (nat_lit 1106709) (nat_lit 1461484267) (nat_lit 0) D2M8K2.u377 from rfl, allE_node, arows370, irow378, arows377]
  all_goals rfl

theorem atot378 : totK PD2M8K2 D2M8K2.u378 = [0, 2112626494489, 6583919209165, 4758529939134, 692476356209, 18797058808, 0, 0] := by
  rw [show D2M8K2.u378 = KTree.node D2M8K2.u370 (nat_lit 1106709) (nat_lit 1461484267) (nat_lit 0) D2M8K2.u377 from rfl, totK_node, atot370, atot377]
  decide +kernel

theorem arows396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u396 = true := by
  rw [show D2M8K2.u396 = KTree.node D2M8K2.u388 (nat_lit 1167498) (nat_lit 3704873797) (nat_lit 0) D2M8K2.u395 from rfl, allE_node, arows388, irow396, arows395]
  all_goals rfl

theorem atot396 : totK PD2M8K2 D2M8K2.u396 = [1545881644484, 5589036028359, 5653101214035, 1524988735005, 77808499359, 0, 0, 0] := by
  rw [show D2M8K2.u396 = KTree.node D2M8K2.u388 (nat_lit 1167498) (nat_lit 3704873797) (nat_lit 0) D2M8K2.u395 from rfl, totK_node, atot388, atot395]
  decide +kernel

theorem arows411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u411 = true := by
  rw [show D2M8K2.u411 = KTree.node D2M8K2.u403 (nat_lit 1185868) (nat_lit 3855143072) (nat_lit 0) D2M8K2.u410 from rfl, allE_node, arows403, irow411, arows410]
  all_goals rfl

theorem atot411 : totK PD2M8K2 D2M8K2.u411 = [435809923056, 3546796546378, 6850337898171, 3217663698873, 247812514485, 1138244013, 0, 0] := by
  rw [show D2M8K2.u411 = KTree.node D2M8K2.u403 (nat_lit 1185868) (nat_lit 3855143072) (nat_lit 0) D2M8K2.u410 from rfl, totK_node, atot403, atot410]
  decide +kernel

theorem arows427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u427 = true := by
  rw [show D2M8K2.u427 = KTree.node D2M8K2.u419 (nat_lit 1208352) (nat_lit 2242088954) (nat_lit 0) D2M8K2.u426 from rfl, allE_node, arows419, irow427, arows426]
  all_goals rfl

theorem atot427 : totK PD2M8K2 D2M8K2.u427 = [1552995635342, 5289814186760, 5388973896072, 1945186137407, 242903562308, 4977114383, 0, 0] := by
  rw [show D2M8K2.u427 = KTree.node D2M8K2.u419 (nat_lit 1208352) (nat_lit 2242088954) (nat_lit 0) D2M8K2.u426 from rfl, totK_node, atot419, atot426]
  decide +kernel

theorem arows442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u442 = true := by
  rw [show D2M8K2.u442 = KTree.node D2M8K2.u434 (nat_lit 1225233) (nat_lit 1687467696) (nat_lit 0) D2M8K2.u441 from rfl, allE_node, arows434, irow442, arows441]
  all_goals rfl

theorem atot442 : totK PD2M8K2 D2M8K2.u442 = [440265286504, 3184011495923, 6475795669889, 3843570098013, 438233588788, 6190125969, 0, 0] := by
  rw [show D2M8K2.u442 = KTree.node D2M8K2.u434 (nat_lit 1225233) (nat_lit 1687467696) (nat_lit 0) D2M8K2.u441 from rfl, totK_node, atot434, atot441]
  decide +kernel

theorem arows459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u459 = true := by
  rw [show D2M8K2.u459 = KTree.node D2M8K2.u451 (nat_lit 1245157) (nat_lit 1354391865) (nat_lit 0) D2M8K2.u458 from rfl, allE_node, arows451, irow459, arows458]
  all_goals rfl

theorem atot459 : totK PD2M8K2 D2M8K2.u459 = [0, 1733239001199, 5994096796687, 5476439661155, 1113989944639, 41101450378, 0, 0] := by
  rw [show D2M8K2.u459 = KTree.node D2M8K2.u451 (nat_lit 1245157) (nat_lit 1354391865) (nat_lit 0) D2M8K2.u458 from rfl, totK_node, atot451, atot458]
  decide +kernel

theorem arows474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u474 = true := by
  rw [show D2M8K2.u474 = KTree.node D2M8K2.u466 (nat_lit 1263253) (nat_lit 1232583596) (nat_lit 0) D2M8K2.u473 from rfl, allE_node, arows466, irow474, arows473]
  all_goals rfl

theorem atot474 : totK PD2M8K2 D2M8K2.u474 = [0, 906932737198, 4518137888877, 6359056456083, 2225128243593, 163736051145, 1275377855, 0] := by
  rw [show D2M8K2.u474 = KTree.node D2M8K2.u466 (nat_lit 1263253) (nat_lit 1232583596) (nat_lit 0) D2M8K2.u473 from rfl, totK_node, atot466, atot473]
  decide +kernel

theorem arows490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u490 = true := by
  rw [show D2M8K2.u490 = KTree.node D2M8K2.u482 (nat_lit 1291605) (nat_lit 1094904733) (nat_lit 0) D2M8K2.u489 from rfl, allE_node, arows482, irow490, arows489]
  all_goals rfl

theorem atot490 : totK PD2M8K2 D2M8K2.u490 = [0, 1254475376028, 5205133103440, 6100623292565, 1761556831919, 80535546629, 0, 0] := by
  rw [show D2M8K2.u490 = KTree.node D2M8K2.u482 (nat_lit 1291605) (nat_lit 1094904733) (nat_lit 0) D2M8K2.u489 from rfl, totK_node, atot482, atot489]
  decide +kernel

theorem arows505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u505 = true := by
  rw [show D2M8K2.u505 = KTree.node D2M8K2.u497 (nat_lit 1329465) (nat_lit 1835229511) (nat_lit 0) D2M8K2.u504 from rfl, allE_node, arows497, irow505, arows504]
  all_goals rfl

theorem atot505 : totK PD2M8K2 D2M8K2.u505 = [0, 1672927024889, 5858371167287, 5586781527357, 1272665155264, 48259591619, 0, 0] := by
  rw [show D2M8K2.u505 = KTree.node D2M8K2.u497 (nat_lit 1329465) (nat_lit 1835229511) (nat_lit 0) D2M8K2.u504 from rfl, totK_node, atot497, atot504]
  decide +kernel

theorem arows525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u525 = true := by
  rw [show D2M8K2.u525 = KTree.node D2M8K2.u517 (nat_lit 1346312) (nat_lit 3152299909) (nat_lit 0) D2M8K2.u524 from rfl, allE_node, arows517, irow525, arows524]
  all_goals rfl

theorem atot525 : totK PD2M8K2 D2M8K2.u525 = [0, 834584878615, 4326803854895, 6404066807067, 2456862489273, 195553639498, 1206465782, 0] := by
  rw [show D2M8K2.u525 = KTree.node D2M8K2.u517 (nat_lit 1346312) (nat_lit 3152299909) (nat_lit 0) D2M8K2.u524 from rfl, totK_node, atot517, atot524]
  decide +kernel

theorem arows540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u540 = true := by
  rw [show D2M8K2.u540 = KTree.node D2M8K2.u532 (nat_lit 1365850) (nat_lit 3808469700) (nat_lit 0) D2M8K2.u539 from rfl, allE_node, arows532, irow540, arows539]
  all_goals rfl

theorem atot540 : totK PD2M8K2 D2M8K2.u540 = [0, 794123137510, 3813266265494, 5869041116242, 3137254005433, 504971212521, 17590593026, 0] := by
  rw [show D2M8K2.u540 = KTree.node D2M8K2.u532 (nat_lit 1365850) (nat_lit 3808469700) (nat_lit 0) D2M8K2.u539 from rfl, totK_node, atot532, atot539]
  decide +kernel

theorem arows556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u556 = true := by
  rw [show D2M8K2.u556 = KTree.node D2M8K2.u548 (nat_lit 1424187) (nat_lit 3787140926) (nat_lit 0) D2M8K2.u555 from rfl, allE_node, arows548, irow556, arows555]
  all_goals rfl

theorem atot556 : totK PD2M8K2 D2M8K2.u556 = [0, 1183320114412, 4919607788344, 6053450448372, 1942868172421, 123360606799, 1103454931, 0] := by
  rw [show D2M8K2.u556 = KTree.node D2M8K2.u548 (nat_lit 1424187) (nat_lit 3787140926) (nat_lit 0) D2M8K2.u555 from rfl, totK_node, atot548, atot555]
  decide +kernel

theorem arows571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u571 = true := by
  rw [show D2M8K2.u571 = KTree.node D2M8K2.u563 (nat_lit 1451644) (nat_lit 3828659917) (nat_lit 0) D2M8K2.u570 from rfl, allE_node, arows563, irow571, arows570]
  all_goals rfl

theorem atot571 : totK PD2M8K2 D2M8K2.u571 = [0, 882293740363, 4275799234136, 6250490340975, 2566246518297, 241415514489, 4779662215, 0] := by
  rw [show D2M8K2.u571 = KTree.node D2M8K2.u563 (nat_lit 1451644) (nat_lit 3828659917) (nat_lit 0) D2M8K2.u570 from rfl, totK_node, atot563, atot570]
  decide +kernel

theorem arows588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u588 = true := by
  rw [show D2M8K2.u588 = KTree.node D2M8K2.u580 (nat_lit 1469488) (nat_lit 3428332739) (nat_lit 0) D2M8K2.u587 from rfl, allE_node, arows580, irow588, arows587]
  all_goals rfl

theorem atot588 : totK PD2M8K2 D2M8K2.u588 = [613088067924, 3065004341602, 5530087968864, 4284611292434, 953148085655, 36795064199, 0, 0] := by
  rw [show D2M8K2.u588 = KTree.node D2M8K2.u580 (nat_lit 1469488) (nat_lit 3428332739) (nat_lit 0) D2M8K2.u587 from rfl, totK_node, atot580, atot587]
  decide +kernel

theorem arows603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u603 = true := by
  rw [show D2M8K2.u603 = KTree.node D2M8K2.u595 (nat_lit 1507596) (nat_lit 3030158248) (nat_lit 0) D2M8K2.u602 from rfl, allE_node, arows595, irow603, arows602]
  all_goals rfl

theorem atot603 : totK PD2M8K2 D2M8K2.u603 = [1416642722751, 5447760529575, 5885955361198, 1523124130381, 62940620160, 0, 0, 0] := by
  rw [show D2M8K2.u603 = KTree.node D2M8K2.u595 (nat_lit 1507596) (nat_lit 3030158248) (nat_lit 0) D2M8K2.u602 from rfl, totK_node, atot595, atot602]
  decide +kernel

theorem arows619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u619 = true := by
  rw [show D2M8K2.u619 = KTree.node D2M8K2.u611 (nat_lit 1528371) (nat_lit 2408440221) (nat_lit 0) D2M8K2.u618 from rfl, allE_node, arows611, irow619, arows618]
  all_goals rfl

theorem atot619 : totK PD2M8K2 D2M8K2.u619 = [434179821839, 3350692223487, 6789882080570, 3483578398209, 294794115377, 1369150432, 0, 0] := by
  rw [show D2M8K2.u619 = KTree.node D2M8K2.u611 (nat_lit 1528371) (nat_lit 2408440221) (nat_lit 0) D2M8K2.u618 from rfl, totK_node, atot611, atot618]
  decide +kernel

theorem arows634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u634 = true := by
  rw [show D2M8K2.u634 = KTree.node D2M8K2.u626 (nat_lit 1551795) (nat_lit 2456686291) (nat_lit 0) D2M8K2.u633 from rfl, allE_node, arows626, irow634, arows633]
  all_goals rfl

theorem atot634 : totK PD2M8K2 D2M8K2.u634 = [1228700755163, 4817694820842, 5695228461493, 2296179742897, 431602526235, 29044448997, 0, 0] := by
  rw [show D2M8K2.u634 = KTree.node D2M8K2.u626 (nat_lit 1551795) (nat_lit 2456686291) (nat_lit 0) D2M8K2.u633 from rfl, totK_node, atot626, atot633]
  decide +kernel

theorem arows652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u652 = true := by
  rw [show D2M8K2.u652 = KTree.node D2M8K2.u644 (nat_lit 1571943) (nat_lit 2890000784) (nat_lit 0) D2M8K2.u651 from rfl, allE_node, arows644, irow652, arows651]
  all_goals rfl

theorem atot652 : totK PD2M8K2 D2M8K2.u652 = [437729727136, 2725009783797, 5763014731127, 4531944771628, 929668345145, 23813810311, 0, 0] := by
  rw [show D2M8K2.u652 = KTree.node D2M8K2.u644 (nat_lit 1571943) (nat_lit 2890000784) (nat_lit 0) D2M8K2.u651 from rfl, totK_node, atot644, atot651]
  decide +kernel

theorem arows667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u667 = true := by
  rw [show D2M8K2.u667 = KTree.node D2M8K2.u659 (nat_lit 1630604) (nat_lit 3172335785) (nat_lit 0) D2M8K2.u666 from rfl, allE_node, arows659, irow667, arows666]
  all_goals rfl

theorem atot667 : totK PD2M8K2 D2M8K2.u667 = [1669786716667, 5811131799109, 5573439814488, 1333636137871, 53975111986, 0, 0, 0] := by
  rw [show D2M8K2.u667 = KTree.node D2M8K2.u659 (nat_lit 1630604) (nat_lit 3172335785) (nat_lit 0) D2M8K2.u666 from rfl, totK_node, atot659, atot666]
  decide +kernel

theorem arows683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u683 = true := by
  rw [show D2M8K2.u683 = KTree.node D2M8K2.u675 (nat_lit 1649462) (nat_lit 3968625444) (nat_lit 0) D2M8K2.u682 from rfl, allE_node, arows675, irow683, arows682]
  all_goals rfl

theorem atot683 : totK PD2M8K2 D2M8K2.u683 = [0, 2097695269902, 6551164328198, 4831608475867, 710756951004, 19065934916, 0, 0] := by
  rw [show D2M8K2.u683 = KTree.node D2M8K2.u675 (nat_lit 1649462) (nat_lit 3968625444) (nat_lit 0) D2M8K2.u682 from rfl, totK_node, atot675, atot682]
  decide +kernel

theorem arows698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u698 = true := by
  rw [show D2M8K2.u698 = KTree.node D2M8K2.u690 (nat_lit 1664963) (nat_lit 2759426660) (nat_lit 0) D2M8K2.u697 from rfl, allE_node, arows690, irow698, arows697]
  all_goals rfl

theorem atot698 : totK PD2M8K2 D2M8K2.u698 = [1546055658120, 5524994992029, 5630509931268, 1601723698081, 86275257928, 0, 0, 0] := by
  rw [show D2M8K2.u698 = KTree.node D2M8K2.u690 (nat_lit 1664963) (nat_lit 2759426660) (nat_lit 0) D2M8K2.u697 from rfl, totK_node, atot690, atot697]
  decide +kernel

theorem arows715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u715 = true := by
  rw [show D2M8K2.u715 = KTree.node D2M8K2.u707 (nat_lit 1682866) (nat_lit 3891556122) (nat_lit 0) D2M8K2.u714 from rfl, allE_node, arows707, irow715, arows714]
  all_goals rfl

theorem atot715 : totK PD2M8K2 D2M8K2.u715 = [435828682369, 3567122183052, 6868240465179, 3192236108163, 241663134092, 1138244013, 0, 0] := by
  rw [show D2M8K2.u715 = KTree.node D2M8K2.u707 (nat_lit 1682866) (nat_lit 3891556122) (nat_lit 0) D2M8K2.u714 from rfl, totK_node, atot707, atot714]
  decide +kernel

theorem arows730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u730 = true := by
  rw [show D2M8K2.u730 = KTree.node D2M8K2.u722 (nat_lit 1705856) (nat_lit 3757458744) (nat_lit 0) D2M8K2.u729 from rfl, allE_node, arows722, irow730, arows729]
  all_goals rfl

theorem atot730 : totK PD2M8K2 D2M8K2.u730 = [1553184942750, 5284748417973, 5391472964508, 1963735561036, 244678839249, 4977114383, 0, 0] := by
  rw [show D2M8K2.u730 = KTree.node D2M8K2.u722 (nat_lit 1705856) (nat_lit 3757458744) (nat_lit 0) D2M8K2.u729 from rfl, totK_node, atot722, atot729]
  decide +kernel

theorem arows746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u746 = true := by
  rw [show D2M8K2.u746 = KTree.node D2M8K2.u738 (nat_lit 1722685) (nat_lit 1261894060) (nat_lit 0) D2M8K2.u745 from rfl, allE_node, arows738, irow746, arows745]
  all_goals rfl

theorem atot746 : totK PD2M8K2 D2M8K2.u746 = [440289439084, 3269619134715, 6487028581866, 3780504293817, 437880727819, 6190125969, 0, 0] := by
  rw [show D2M8K2.u746 = KTree.node D2M8K2.u738 (nat_lit 1722685) (nat_lit 1261894060) (nat_lit 0) D2M8K2.u745 from rfl, totK_node, atot738, atot745]
  decide +kernel

theorem arows761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u761 = true := by
  rw [show D2M8K2.u761 = KTree.node D2M8K2.u753 (nat_lit 1742652) (nat_lit 2765978224) (nat_lit 0) D2M8K2.u760 from rfl, allE_node, arows753, irow761, arows760]
  all_goals rfl

theorem atot761 : totK PD2M8K2 D2M8K2.u761 = [0, 1808830694867, 6227563656417, 5329324682975, 943444155727, 29216042764, 0, 0] := by
  rw [show D2M8K2.u761 = KTree.node D2M8K2.u753 (nat_lit 1742652) (nat_lit 2765978224) (nat_lit 0) D2M8K2.u760 from rfl, totK_node, atot753, atot760]
  decide +kernel

theorem arows780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u780 = true := by
  rw [show D2M8K2.u780 = KTree.node D2M8K2.u772 (nat_lit 1760704) (nat_lit 3003537097) (nat_lit 0) D2M8K2.u779 from rfl, allE_node, arows772, irow780, arows779]
  all_goals rfl

theorem atot780 : totK PD2M8K2 D2M8K2.u780 = [0, 831932393438, 4413125948917, 6470480853422, 2281958986713, 160323929045, 1310517177, 0] := by
  rw [show D2M8K2.u780 = KTree.node D2M8K2.u772 (nat_lit 1760704) (nat_lit 3003537097) (nat_lit 0) D2M8K2.u779 from rfl, totK_node, atot772, atot779]
  decide +kernel

theorem arows795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u795 = true := by
  rw [show D2M8K2.u795 = KTree.node D2M8K2.u787 (nat_lit 1788955) (nat_lit 1698073983) (nat_lit 0) D2M8K2.u794 from rfl, allE_node, arows787, irow795, arows794]
  all_goals rfl

theorem atot795 : totK PD2M8K2 D2M8K2.u795 = [0, 1200471089959, 4928478979189, 6140179518886, 2014149830740, 101901463567, 0, 0] := by
  rw [show D2M8K2.u795 = KTree.node D2M8K2.u787 (nat_lit 1788955) (nat_lit 1698073983) (nat_lit 0) D2M8K2.u794 from rfl, totK_node, atot787, atot794]
  decide +kernel

theorem arows811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u811 = true := by
  rw [show D2M8K2.u811 = KTree.node D2M8K2.u803 (nat_lit 1867828) (nat_lit 3642273319) (nat_lit 0) D2M8K2.u810 from rfl, allE_node, arows803, irow811, arows810]
  all_goals rfl

theorem atot811 : totK PD2M8K2 D2M8K2.u811 = [0, 1639320630375, 5844033506771, 5572997698434, 1310529195927, 53227534193, 0, 0] := by
  rw [show D2M8K2.u811 = KTree.node D2M8K2.u803 (nat_lit 1867828) (nat_lit 3642273319) (nat_lit 0) D2M8K2.u810 from rfl, totK_node, atot803, atot810]
  decide +kernel

theorem arows826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u826 = true := by
  rw [show D2M8K2.u826 = KTree.node D2M8K2.u818 (nat_lit 1884563) (nat_lit 2739261758) (nat_lit 0) D2M8K2.u825 from rfl, allE_node, arows818, irow826, arows825]
  all_goals rfl

theorem atot826 : totK PD2M8K2 D2M8K2.u826 = [0, 923688535341, 4461416888159, 6310406871972, 2340842243751, 178539333049, 1217496766, 0] := by
  rw [show D2M8K2.u826 = KTree.node D2M8K2.u818 (nat_lit 1884563) (nat_lit 2739261758) (nat_lit 0) D2M8K2.u825 from rfl, totK_node, atot818, atot825]
  decide +kernel

theorem arows843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u843 = true := by
  rw [show D2M8K2.u843 = KTree.node D2M8K2.u835 (nat_lit 1904272) (nat_lit 3106720821) (nat_lit 0) D2M8K2.u842 from rfl, allE_node, arows835, irow843, arows842]
  all_goals rfl

theorem atot843 : totK PD2M8K2 D2M8K2.u843 = [0, 795078674787, 3771318459566, 5861998009260, 3206327612816, 520051401163, 17736366219, 0] := by
  rw [show D2M8K2.u843 = KTree.node D2M8K2.u835 (nat_lit 1904272) (nat_lit 3106720821) (nat_lit 0) D2M8K2.u842 from rfl, totK_node, atot835, atot842]
  decide +kernel

theorem arows858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u858 = true := by
  rw [show D2M8K2.u858 = KTree.node D2M8K2.u850 (nat_lit 1920908) (nat_lit 3172335785) (nat_lit 0) D2M8K2.u857 from rfl, allE_node, arows850, irow858, arows857]
  all_goals rfl

theorem atot858 : totK PD2M8K2 D2M8K2.u858 = [0, 1184050639701, 4904900944164, 6029935417015, 1973545037636, 125181334779, 1138244013, 0] := by
  rw [show D2M8K2.u858 = KTree.node D2M8K2.u850 (nat_lit 1920908) (nat_lit 3172335785) (nat_lit 0) D2M8K2.u857 from rfl, totK_node, atot850, atot857]
  decide +kernel

theorem arows874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u874 = true := by
  rw [show D2M8K2.u874 = KTree.node D2M8K2.u866 (nat_lit 1944127) (nat_lit 1728858215) (nat_lit 0) D2M8K2.u873 from rfl, allE_node, arows866, irow874, arows873]
  all_goals rfl

theorem atot874 : totK PD2M8K2 D2M8K2.u874 = [0, 798340129520, 4180849177082, 6335766870483, 2653334101975, 255375201114, 4914284239, 0] := by
  rw [show D2M8K2.u874 = KTree.node D2M8K2.u866 (nat_lit 1944127) (nat_lit 1728858215) (nat_lit 0) D2M8K2.u873 from rfl, totK_node, atot866, atot873]
  decide +kernel

theorem arows889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u889 = true := by
  rw [show D2M8K2.u889 = KTree.node D2M8K2.u881 (nat_lit 1962528) (nat_lit 3456965496) (nat_lit 0) D2M8K2.u888 from rfl, allE_node, arows881, irow889, arows888]
  all_goals rfl

theorem atot889 : totK PD2M8K2 D2M8K2.u889 = [437191058986, 2461047196697, 5303124806466, 4886057792410, 1286237293951, 52413581636, 0, 0] := by
  rw [show D2M8K2.u889 = KTree.node D2M8K2.u881 (nat_lit 1962528) (nat_lit 3456965496) (nat_lit 0) D2M8K2.u888 from rfl, totK_node, atot881, atot888]
  decide +kernel

theorem arows907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u907 = true := by
  rw [show D2M8K2.u907 = KTree.node D2M8K2.u899 (nat_lit 2003706) (nat_lit 3943699390) (nat_lit 0) D2M8K2.u906 from rfl, allE_node, arows899, irow907, arows906]
  all_goals rfl

theorem atot907 : totK PD2M8K2 D2M8K2.u907 = [1590605213906, 5824884210436, 5715466423132, 1208047634844, 37314027372, 0, 0, 0] := by
  rw [show D2M8K2.u907 = KTree.node D2M8K2.u899 (nat_lit 2003706) (nat_lit 3943699390) (nat_lit 0) D2M8K2.u906 from rfl, totK_node, atot899, atot906]
  decide +kernel

theorem arows922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u922 = true := by
  rw [show D2M8K2.u922 = KTree.node D2M8K2.u914 (nat_lit 2022958) (nat_lit 2542186155) (nat_lit 0) D2M8K2.u921 from rfl, allE_node, arows914, irow922, arows921]
  all_goals rfl

theorem atot922 : totK PD2M8K2 D2M8K2.u922 = [430146303138, 3362388188903, 6775443659147, 3454824802265, 301300337120, 1369150432, 0, 0] := by
  rw [show D2M8K2.u922 = KTree.node D2M8K2.u914 (nat_lit 2022958) (nat_lit 2542186155) (nat_lit 0) D2M8K2.u921 from rfl, totK_node, atot914, atot921]
  decide +kernel

theorem arows938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u938 = true := by
  rw [show D2M8K2.u938 = KTree.node D2M8K2.u930 (nat_lit 2044345) (nat_lit 1469226153) (nat_lit 0) D2M8K2.u937 from rfl, allE_node, arows930, irow938, arows937]
  all_goals rfl

theorem atot938 : totK PD2M8K2 D2M8K2.u938 = [1228971012768, 5082012562881, 6112911453199, 1950086356630, 106456485469, 0, 0, 0] := by
  rw [show D2M8K2.u938 = KTree.node D2M8K2.u930 (nat_lit 2044345) (nat_lit 1469226153) (nat_lit 0) D2M8K2.u937 from rfl, totK_node, atot930, atot937]
  decide +kernel

theorem arows953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u953 = true := by
  rw [show D2M8K2.u953 = KTree.node D2M8K2.u945 (nat_lit 2064806) (nat_lit 4005331914) (nat_lit 0) D2M8K2.u952 from rfl, allE_node, arows945, irow953, arows952]
  all_goals rfl

theorem atot953 : totK PD2M8K2 D2M8K2.u953 = [409976030251, 2358529326157, 5389659752768, 4972956043997, 1187592284342, 48715757244, 0, 0] := by
  rw [show D2M8K2.u953 = KTree.node D2M8K2.u945 (nat_lit 2064806) (nat_lit 4005331914) (nat_lit 0) D2M8K2.u952 from rfl, totK_node, atot945, atot952]
  decide +kernel

theorem arows970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u970 = true := by
  rw [show D2M8K2.u970 = KTree.node D2M8K2.u962 (nat_lit 2082344) (nat_lit 3832618542) (nat_lit 0) D2M8K2.u969 from rfl, allE_node, arows962, irow970, arows969]
  all_goals rfl

theorem atot970 : totK PD2M8K2 D2M8K2.u970 = [1575236328664, 5715845965201, 5733706309053, 1379143654883, 56939016946, 0, 0, 0] := by
  rw [show D2M8K2.u970 = KTree.node D2M8K2.u962 (nat_lit 2082344) (nat_lit 3832618542) (nat_lit 0) D2M8K2.u969 from rfl, totK_node, atot962, atot969]
  decide +kernel

theorem arows985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u985 = true := by
  rw [show D2M8K2.u985 = KTree.node D2M8K2.u977 (nat_lit 2102038) (nat_lit 2987652673) (nat_lit 0) D2M8K2.u984 from rfl, allE_node, arows977, irow985, arows984]
  all_goals rfl

theorem atot985 : totK PD2M8K2 D2M8K2.u985 = [0, 2138873663749, 6598603799658, 4728191472415, 693028317702, 18797058808, 0, 0] := by
  rw [show D2M8K2.u985 = KTree.node D2M8K2.u977 (nat_lit 2102038) (nat_lit 2987652673) (nat_lit 0) D2M8K2.u984 from rfl, totK_node, atot977, atot984]
  decide +kernel

theorem arows1001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1001 = true := by
  rw [show D2M8K2.u1001 = KTree.node D2M8K2.u993 (nat_lit 2121736) (nat_lit 3353397405) (nat_lit 0) D2M8K2.u1000 from rfl, allE_node, arows993, irow1001, arows1000]
  all_goals rfl

theorem atot1001 : totK PD2M8K2 D2M8K2.u1001 = [1656458230744, 5807523148483, 5561440646515, 1352712439994, 65526037469, 0, 0, 0] := by
  rw [show D2M8K2.u1001 = KTree.node D2M8K2.u993 (nat_lit 2121736) (nat_lit 3353397405) (nat_lit 0) D2M8K2.u1000 from rfl, totK_node, atot993, atot1000]
  decide +kernel

theorem arows1016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1016 = true := by
  rw [show D2M8K2.u1016 = KTree.node D2M8K2.u1008 (nat_lit 2139879) (nat_lit 3631119225) (nat_lit 0) D2M8K2.u1015 from rfl, allE_node, arows1008, irow1016, arows1015]
  all_goals rfl

theorem atot1016 : totK PD2M8K2 D2M8K2.u1016 = [329265630786, 2927267034134, 6503279930718, 4001160252699, 534504200965, 14345316470, 0, 0] := by
  rw [show D2M8K2.u1016 = KTree.node D2M8K2.u1008 (nat_lit 2139879) (nat_lit 3631119225) (nat_lit 0) D2M8K2.u1015 from rfl, totK_node, atot1008, atot1015]
  decide +kernel

end QECKChecks.D2M8K2
