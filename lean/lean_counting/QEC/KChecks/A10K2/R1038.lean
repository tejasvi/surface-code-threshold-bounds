import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4152 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4152 = true := by
  decide +kernel

theorem tot4152 : totK PA10K2 A10K2.t4152 = [0, 497548885211, 1853980305425, 1971660010362, 526087761791, 31301336365, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4153 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4153 = true := by
  decide +kernel

theorem tot4153 : totK PA10K2 A10K2.t4153 = [0, 0, 738960610133, 2126881122065, 1623603153325, 376235219210, 25313348169, 0, 0, 0] := by
  decide +kernel

theorem rows4154 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4154 = true := by
  decide +kernel

theorem tot4154 : totK PA10K2 A10K2.t4154 = [0, 280443219282, 1375422719662, 2185749033706, 1083759739855, 98668773074, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4155 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4155 = true := by
  decide +kernel

theorem tot4155 : totK PA10K2 A10K2.t4155 = [0, 326500081170, 1450975230589, 2156583407864, 1028236191200, 115271257396, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
