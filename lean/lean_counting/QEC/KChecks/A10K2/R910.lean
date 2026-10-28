import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3640 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3640 = true := by
  decide +kernel

theorem tot3640 : totK PA10K2 A10K2.t3640 = [0, 0, 551711484753, 1925986768304, 1949131357034, 543434629556, 31947994545, 0, 0, 0] := by
  decide +kernel

theorem rows3641 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3641 = true := by
  decide +kernel

theorem tot3641 : totK PA10K2 A10K2.t3641 = [0, 0, 17059334586, 893069975464, 2268137959820, 1591194942402, 263504895073, 7047025452, 0, 0] := by
  decide +kernel

theorem rows3642 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3642 = true := by
  decide +kernel

theorem tot3642 : totK PA10K2 A10K2.t3642 = [0, 0, 481299516846, 1736625403398, 2062378402203, 830708685099, 62351542051, 0, 0, 0] := by
  decide +kernel

theorem rows3643 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3643 = true := by
  decide +kernel

theorem tot3643 : totK PA10K2 A10K2.t3643 = [0, 0, 316440062743, 1592154162549, 2233120061458, 857719718756, 62972848401, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
