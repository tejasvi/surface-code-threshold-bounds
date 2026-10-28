import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3624 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3624 = true := by
  decide +kernel

theorem tot3624 : totK PA10K2 A10K2.t3624 = [0, 136213957219, 979374376610, 2013856311910, 1509916301901, 369614510231, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows3625 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3625 = true := by
  decide +kernel

theorem tot3625 : totK PA10K2 A10K2.t3625 = [0, 226848922415, 1047721864731, 1860306375782, 1369439843966, 246449247915, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows3626 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3626 = true := by
  decide +kernel

theorem tot3626 : totK PA10K2 A10K2.t3626 = [0, 461027229870, 1637529810788, 1895147704954, 663770615300, 52232171148, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3627 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3627 = true := by
  decide +kernel

theorem tot3627 : totK PA10K2 A10K2.t3627 = [0, 112111361307, 1265814888629, 2270600626078, 991933766153, 74092660947, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
