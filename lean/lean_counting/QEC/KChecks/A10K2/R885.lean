import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3540 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3540 = true := by
  decide +kernel

theorem tot3540 : totK PA10K2 A10K2.t3540 = [0, 0, 0, 291400714472, 1253358743729, 1864427122518, 1130308907429, 209648264322, 5517381808, 0] := by
  decide +kernel

theorem rows3541 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3541 = true := by
  decide +kernel

theorem tot3541 : totK PA10K2 A10K2.t3541 = [0, 0, 0, 462922208630, 1840615940959, 1962564405493, 546978344768, 32659299833, 0, 0] := by
  decide +kernel

theorem rows3542 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3542 = true := by
  decide +kernel

theorem tot3542 : totK PA10K2 A10K2.t3542 = [0, 0, 0, 614334841668, 2040233754490, 1892274369093, 463596743599, 25788972206, 0, 0] := by
  decide +kernel

theorem rows3543 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3543 = true := by
  decide +kernel

theorem tot3543 : totK PA10K2 A10K2.t3543 = [0, 0, 424471676933, 1348089399782, 1548943131338, 1150243167511, 525095170489, 42727170192, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
