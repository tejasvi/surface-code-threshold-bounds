import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4312 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4312 = true := by
  decide +kernel

theorem tot4312 : totK PA10K2 A10K2.t4312 = [0, 56979818624, 71026307435, 786129983549, 2130115748812, 1295194688031, 193534632719, 5976421810, 0, 0] := by
  decide +kernel

theorem rows4313 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4313 = true := by
  decide +kernel

theorem tot4313 : totK PA10K2 A10K2.t4313 = [0, 520717301057, 1867488081063, 1938897274434, 538710807849, 31989350221, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4314 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4314 = true := by
  decide +kernel

theorem tot4314 : totK PA10K2 A10K2.t4314 = [0, 230931049285, 1305412125431, 2192930377116, 1112038524976, 114785144961, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4315 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4315 = true := by
  decide +kernel

theorem tot4315 : totK PA10K2 A10K2.t4315 = [0, 81682682322, 674431022875, 1829597402095, 1730293648342, 476267493731, 30810868011, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
