import QEC.Count.ChunksK3
import QEC.KChecks.A6K2.R0
import QEC.KChecks.A6K2.R1
import QEC.KChecks.A6K2.R2
import QEC.KChecks.A6K2.R3
import QEC.KChecks.A6K2.R4
import QEC.KChecks.A6K2.R5
import QEC.KChecks.A6K2.R6
import QEC.KChecks.A6K2.R7
import QEC.KChecks.A6K2.R8
import QEC.KChecks.A6K2.R9
import QEC.KChecks.A6K2.R10
import QEC.KChecks.A6K2.R11
import QEC.KChecks.A6K2.R12
import QEC.KChecks.A6K2.R13
import QEC.KChecks.A6K2.R14
import QEC.KChecks.A6K2.R15
import QEC.KChecks.A6K2.I0

namespace QECKChecks.A6K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows0 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.u0 = true := by
  rw [show A6K2.u0 = KTree.node A6K2.t0 (nat_lit 2275) (nat_lit 10863738889) (nat_lit 0) A6K2.t1 from rfl, allE_node, rows0, irow0, rows1]
  all_goals rfl

theorem atot0 : totK PA6K2 A6K2.u0 = [966286715158, 3441799844628, 3504636929214, 927800345471, 44286290707, 0] := by
  rw [show A6K2.u0 = KTree.node A6K2.t0 (nat_lit 2275) (nat_lit 10863738889) (nat_lit 0) A6K2.t1 from rfl, totK_node, tot0, tot1]
  decide +kernel

theorem arows1 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.u1 = true := by
  rw [show A6K2.u1 = KTree.node A6K2.t2 (nat_lit 6178) (nat_lit 9399746397) (nat_lit 0) A6K2.t3 from rfl, allE_node, rows2, irow1, rows3]
  all_goals rfl

theorem atot1 : totK PA6K2 A6K2.u1 = [44336571969, 1149846320725, 3676953186436, 3218896001098, 688221378964, 36473236577] := by
  rw [show A6K2.u1 = KTree.node A6K2.t2 (nat_lit 6178) (nat_lit 9399746397) (nat_lit 0) A6K2.t3 from rfl, totK_node, tot2, tot3]
  decide +kernel

theorem arows3 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.u3 = true := by
  rw [show A6K2.u3 = KTree.node A6K2.t4 (nat_lit 10496) (nat_lit 15171530017) (nat_lit 0) A6K2.t5 from rfl, allE_node, rows4, irow3, rows5]
  all_goals rfl

theorem atot3 : totK PA6K2 A6K2.u3 = [922905157643, 3389588944258, 3552399977267, 1009667820370, 45354745260, 0] := by
  rw [show A6K2.u3 = KTree.node A6K2.t4 (nat_lit 10496) (nat_lit 15171530017) (nat_lit 0) A6K2.t5 from rfl, totK_node, tot4, tot5]
  decide +kernel

theorem arows4 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.u4 = true := by
  rw [show A6K2.u4 = KTree.node A6K2.t6 (nat_lit 14378) (nat_lit 9378831097) (nat_lit 0) A6K2.t7 from rfl, allE_node, rows6, irow4, rows7]
  all_goals rfl

theorem atot4 : totK PA6K2 A6K2.u4 = [44103228143, 1137641223371, 3650336438403, 3299244930362, 723239715037, 37541691130] := by
  rw [show A6K2.u4 = KTree.node A6K2.t6 (nat_lit 14378) (nat_lit 9378831097) (nat_lit 0) A6K2.t7 from rfl, totK_node, tot6, tot7]
  decide +kernel

theorem arows7 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.u7 = true := by
  rw [show A6K2.u7 = KTree.node A6K2.t8 (nat_lit 17821) (nat_lit 5634698734) (nat_lit 0) A6K2.t9 from rfl, allE_node, rows8, irow7, rows9]
  all_goals rfl

theorem atot7 : totK PA6K2 A6K2.u7 = [914935524124, 3397569384310, 3471579005906, 948392890165, 60016229439, 0] := by
  rw [show A6K2.u7 = KTree.node A6K2.t8 (nat_lit 17821) (nat_lit 5634698734) (nat_lit 0) A6K2.t9 from rfl, totK_node, tot8, tot9]
  decide +kernel

theorem arows8 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.u8 = true := by
  rw [show A6K2.u8 = KTree.node A6K2.t10 (nat_lit 22640) (nat_lit 15078107739) (nat_lit 0) A6K2.t11 from rfl, allE_node, rows10, irow8, rows11]
  all_goals rfl

theorem atot8 : totK PA6K2 A6K2.u8 = [313961522562, 1962358736962, 3843873792610, 2270602958098, 320635110655, 6999349134] := by
  rw [show A6K2.u8 = KTree.node A6K2.t10 (nat_lit 22640) (nat_lit 15078107739) (nat_lit 0) A6K2.t11 from rfl, totK_node, tot10, tot11]
  decide +kernel

theorem arows10 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.u10 = true := by
  rw [show A6K2.u10 = KTree.node A6K2.t12 (nat_lit 27656) (nat_lit 14850925602) (nat_lit 0) A6K2.t13 from rfl, allE_node, rows12, irow10, rows13]
  all_goals rfl

theorem atot10 : totK PA6K2 A6K2.u10 = [661169677764, 2796160333840, 3783953389797, 1572485190056, 142048837192, 0] := by
  rw [show A6K2.u10 = KTree.node A6K2.t12 (nat_lit 27656) (nat_lit 14850925602) (nat_lit 0) A6K2.t13 from rfl, totK_node, tot12, tot13]
  decide +kernel

theorem arows11 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.u11 = true := by
  rw [show A6K2.u11 = KTree.node A6K2.t14 (nat_lit 30422) (nat_lit 14487558083) (nat_lit 0) A6K2.t15 from rfl, allE_node, rows14, irow11, rows15]
  all_goals rfl

theorem atot11 : totK PA6K2 A6K2.u11 = [0, 856351667339, 3298660091636, 3746709681097, 1152039832937, 76425428331] := by
  rw [show A6K2.u11 = KTree.node A6K2.t14 (nat_lit 30422) (nat_lit 14487558083) (nat_lit 0) A6K2.t15 from rfl, totK_node, tot14, tot15]
  decide +kernel

theorem arows2 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.u2 = true := by
  rw [show A6K2.u2 = KTree.node A6K2.u0 (nat_lit 3770) (nat_lit 15177985847) (nat_lit 0) A6K2.u1 from rfl, allE_node, arows0, irow2, arows1]
  all_goals rfl

theorem atot2 : totK PA6K2 A6K2.u2 = [1010623287127, 4591646165353, 7196768101497, 4146696346569, 732507669671, 36473236577] := by
  rw [show A6K2.u2 = KTree.node A6K2.u0 (nat_lit 3770) (nat_lit 15177985847) (nat_lit 0) A6K2.u1 from rfl, totK_node, atot0, atot1]
  decide +kernel

theorem arows5 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.u5 = true := by
  rw [show A6K2.u5 = KTree.node A6K2.u3 (nat_lit 11995) (nat_lit 7990454993) (nat_lit 0) A6K2.u4 from rfl, allE_node, arows3, irow5, arows4]
  all_goals rfl

theorem atot5 : totK PA6K2 A6K2.u5 = [967008385786, 4527230167629, 7202736415670, 4308912750732, 776584915290, 37541691130] := by
  rw [show A6K2.u5 = KTree.node A6K2.u3 (nat_lit 11995) (nat_lit 7990454993) (nat_lit 0) A6K2.u4 from rfl, totK_node, atot3, atot4]
  decide +kernel

theorem arows9 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.u9 = true := by
  rw [show A6K2.u9 = KTree.node A6K2.u7 (nat_lit 19209) (nat_lit 9852997180) (nat_lit 0) A6K2.u8 from rfl, allE_node, arows7, irow9, arows8]
  all_goals rfl

theorem atot9 : totK PA6K2 A6K2.u9 = [1228897046686, 5359928121272, 7315452798516, 3228848845443, 380651340094, 6999349134] := by
  rw [show A6K2.u9 = KTree.node A6K2.u7 (nat_lit 19209) (nat_lit 9852997180) (nat_lit 0) A6K2.u8 from rfl, totK_node, atot7, atot8]
  decide +kernel

theorem arows12 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.u12 = true := by
  rw [show A6K2.u12 = KTree.node A6K2.u10 (nat_lit 28790) (nat_lit 16470726546) (nat_lit 0) A6K2.u11 from rfl, allE_node, arows10, irow12, arows11]
  all_goals rfl

theorem atot12 : totK PA6K2 A6K2.u12 = [661169677764, 3652512001179, 7099084207979, 5319194871153, 1294088670129, 76425428331] := by
  rw [show A6K2.u12 = KTree.node A6K2.u10 (nat_lit 28790) (nat_lit 16470726546) (nat_lit 0) A6K2.u11 from rfl, totK_node, atot10, atot11]
  decide +kernel

theorem arows6 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.u6 = true := by
  rw [show A6K2.u6 = KTree.node A6K2.u2 (nat_lit 9373) (nat_lit 6766917719) (nat_lit 0) A6K2.u5 from rfl, allE_node, arows2, irow6, arows5]
  all_goals rfl

theorem atot6 : totK PA6K2 A6K2.u6 = [1977631672913, 9118876332982, 14406271434886, 8455609097301, 1509092584961, 74014927707] := by
  rw [show A6K2.u6 = KTree.node A6K2.u2 (nat_lit 9373) (nat_lit 6766917719) (nat_lit 0) A6K2.u5 from rfl, totK_node, atot2, atot5]
  decide +kernel

theorem arows13 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.u13 = true := by
  rw [show A6K2.u13 = KTree.node A6K2.u9 (nat_lit 25136) (nat_lit 15078107739) (nat_lit 0) A6K2.u12 from rfl, allE_node, arows9, irow13, arows12]
  all_goals rfl

theorem atot13 : totK PA6K2 A6K2.u13 = [1890066724450, 9027518230190, 14414537006495, 8548043716596, 1674740010223, 83424777465] := by
  rw [show A6K2.u13 = KTree.node A6K2.u9 (nat_lit 25136) (nat_lit 15078107739) (nat_lit 0) A6K2.u12 from rfl, totK_node, atot9, atot12]
  decide +kernel

theorem arows14 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.u14 = true := by
  rw [show A6K2.u14 = KTree.node A6K2.u6 (nat_lit 16393) (nat_lit 10390662215) (nat_lit 0) A6K2.u13 from rfl, allE_node, arows6, irow14, arows13]
  all_goals rfl

theorem atot14 : totK PA6K2 A6K2.u14 = [3867698397363, 18146394563172, 28831199103596, 17003652813897, 3183832595184, 157439705172] := by
  rw [show A6K2.u14 = KTree.node A6K2.u6 (nat_lit 16393) (nat_lit 10390662215) (nat_lit 0) A6K2.u13 from rfl, totK_node, atot6, atot13]
  decide +kernel

end QECKChecks.A6K2
