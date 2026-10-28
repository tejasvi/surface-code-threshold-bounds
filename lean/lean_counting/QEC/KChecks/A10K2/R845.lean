import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3380 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3380 = true := by
  decide +kernel

theorem tot3380 : totK PA10K2 A10K2.t3380 = [0, 0, 482701838241, 1840040380035, 2032783594229, 608080286019, 29816032797, 0, 0, 0] := by
  decide +kernel

theorem rows3381 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3381 = true := by
  decide +kernel

theorem tot3381 : totK PA10K2 A10K2.t3381 = [0, 0, 0, 594702964498, 2027362361767, 1848510698177, 389367317054, 12219140272, 0, 0] := by
  decide +kernel

theorem rows3382 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3382 = true := by
  decide +kernel

theorem tot3382 : totK PA10K2 A10K2.t3382 = [0, 0, 368468110257, 1517676741839, 2022120411590, 899099451298, 87900005358, 0, 0, 0] := by
  decide +kernel

theorem rows3383 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3383 = true := by
  decide +kernel

theorem tot3383 : totK PA10K2 A10K2.t3383 = [0, 0, 504342033116, 1858730608762, 2044280329979, 637155714386, 30616275043, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
