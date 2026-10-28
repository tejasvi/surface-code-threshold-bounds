import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8020 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8020 = true := by
  decide +kernel

theorem tot8020 : totK PA10K2 A10K2.t8020 = [0, 0, 0, 0, 776661780191, 2276338555787, 1655900409075, 241909040580, 6766355402, 0] := by
  decide +kernel

theorem rows8021 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8021 = true := by
  decide +kernel

theorem tot8021 : totK PA10K2 A10K2.t8021 = [0, 0, 0, 540460088909, 1865519024519, 1915911295139, 620004404942, 50403516269, 0, 0] := by
  decide +kernel

theorem rows8022 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8022 = true := by
  decide +kernel

theorem tot8022 : totK PA10K2 A10K2.t8022 = [0, 0, 0, 327234200007, 1493963329557, 2105395985977, 917211154788, 74360992022, 0, 0] := by
  decide +kernel

theorem rows8023 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8023 = true := by
  decide +kernel

theorem tot8023 : totK PA10K2 A10K2.t8023 = [0, 0, 0, 0, 592246186544, 2040605536031, 1891020366609, 392597080216, 12224107035, 0] := by
  decide +kernel

end QECKChecks.A10K2
