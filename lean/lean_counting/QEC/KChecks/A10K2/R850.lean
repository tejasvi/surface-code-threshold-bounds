import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3400 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3400 = true := by
  decide +kernel

theorem tot3400 : totK PA10K2 A10K2.t3400 = [0, 0, 45770322325, 996143043933, 2376504306513, 1491364002522, 169940475559, 0, 0, 0] := by
  decide +kernel

theorem rows3401 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3401 = true := by
  decide +kernel

theorem tot3401 : totK PA10K2 A10K2.t3401 = [0, 0, 0, 422980327485, 1696500438209, 2061660967767, 714128286575, 47540011751, 0, 0] := by
  decide +kernel

theorem rows3402 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3402 = true := by
  decide +kernel

theorem tot3402 : totK PA10K2 A10K2.t3402 = [0, 0, 0, 463123133898, 1845229656149, 1930747997660, 481477371014, 26479096260, 0, 0] := by
  decide +kernel

theorem rows3403 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3403 = true := by
  decide +kernel

theorem tot3403 : totK PA10K2 A10K2.t3403 = [0, 0, 0, 288681707244, 1403307737737, 2219233461874, 975907296797, 74666917410, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
