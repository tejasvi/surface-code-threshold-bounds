import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7260 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7260 = true := by
  decide +kernel

theorem tot7260 : totK PA10K2 A10K2.t7260 = [0, 0, 565054683428, 1907452513698, 2002236542876, 582673515382, 37383675790, 0, 0, 0] := by
  decide +kernel

theorem rows7261 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7261 = true := by
  decide +kernel

theorem tot7261 : totK PA10K2 A10K2.t7261 = [0, 0, 213388506864, 1332415687255, 2239201910810, 1159448115756, 131063441298, 0, 0, 0] := by
  decide +kernel

theorem rows7262 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7262 = true := by
  decide +kernel

theorem tot7262 : totK PA10K2 A10K2.t7262 = [0, 0, 0, 524584402786, 1936177571305, 2131559351411, 550671232106, 19122223731, 0, 0] := by
  decide +kernel

theorem rows7263 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7263 = true := by
  decide +kernel

theorem tot7263 : totK PA10K2 A10K2.t7263 = [0, 0, 0, 445153688152, 1665553300911, 1956350979959, 723512577602, 68804449356, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
