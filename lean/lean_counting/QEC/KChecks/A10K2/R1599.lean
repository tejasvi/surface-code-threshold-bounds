import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6396 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6396 = true := by
  decide +kernel

theorem tot6396 : totK PA10K2 A10K2.t6396 = [473115181482, 1872611262646, 2063774218075, 563571611499, 32040661968, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6397 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6397 = true := by
  decide +kernel

theorem tot6397 : totK PA10K2 A10K2.t6397 = [0, 659036429108, 2079169407021, 1721631703563, 401474825585, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6398 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6398 = true := by
  decide +kernel

theorem tot6398 : totK PA10K2 A10K2.t6398 = [284639743112, 1291253849077, 2028717905828, 1189663487229, 196849239193, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6399 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6399 = true := by
  decide +kernel

theorem tot6399 : totK PA10K2 A10K2.t6399 = [541450865991, 1956671317138, 2101657592410, 596758652767, 30920017232, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
