import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4512 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4512 = true := by
  decide +kernel

theorem tot4512 : totK PA10K2 A10K2.t4512 = [0, 60623631015, 568804345781, 1767193454884, 1833006925405, 497477115408, 31768748853, 0, 0, 0] := by
  decide +kernel

theorem rows4513 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4513 = true := by
  decide +kernel

theorem tot4513 : totK PA10K2 A10K2.t4513 = [0, 417759118775, 1689653614420, 1901069186689, 631627622841, 51475380808, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4514 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4514 = true := by
  decide +kernel

theorem tot4514 : totK PA10K2 A10K2.t4514 = [0, 298263154340, 1503874101004, 2038481417835, 755278376841, 53438372263, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4515 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4515 = true := by
  decide +kernel

theorem tot4515 : totK PA10K2 A10K2.t4515 = [0, 0, 578391322817, 2082527449771, 1691738705517, 295904979772, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
