import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3636 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3636 = true := by
  decide +kernel

theorem tot3636 : totK PA10K2 A10K2.t3636 = [0, 192465652475, 1115029765325, 2144206259230, 1447109204212, 240875045161, 6032141194, 0, 0, 0] := by
  decide +kernel

theorem rows3637 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3637 = true := by
  decide +kernel

theorem tot3637 : totK PA10K2 A10K2.t3637 = [0, 605984664308, 2044850934838, 1943268517345, 486052154360, 25997994148, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3638 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3638 = true := by
  decide +kernel

theorem tot3638 : totK PA10K2 A10K2.t3638 = [0, 0, 759277067785, 2365629109948, 1815261791936, 269013803999, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3639 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3639 = true := by
  decide +kernel

theorem tot3639 : totK PA10K2 A10K2.t3639 = [0, 0, 543576692558, 1889598327244, 1945659326879, 619423780920, 42874818239, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
