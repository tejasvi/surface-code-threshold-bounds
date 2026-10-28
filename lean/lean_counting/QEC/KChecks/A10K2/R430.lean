import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1720 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1720 = true := by
  decide +kernel

theorem tot1720 : totK PA10K2 A10K2.t1720 = [0, 0, 0, 505068574050, 2031750056040, 2139312450745, 507871044554, 26877458525, 0, 0] := by
  decide +kernel

theorem rows1721 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1721 = true := by
  decide +kernel

theorem tot1721 : totK PA10K2 A10K2.t1721 = [0, 0, 582971723811, 1845885994813, 1649444752119, 599246218085, 183032466980, 23009379923, 0, 0] := by
  decide +kernel

theorem rows1722 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1722 = true := by
  decide +kernel

theorem tot1722 : totK PA10K2 A10K2.t1722 = [0, 0, 203908507248, 1326273862571, 2328149626076, 1064198147238, 86536735702, 0, 0, 0] := by
  decide +kernel

theorem rows1723 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1723 = true := by
  decide +kernel

theorem tot1723 : totK PA10K2 A10K2.t1723 = [0, 0, 49830608282, 558408102102, 1808011602052, 1831753150425, 477621477737, 30831673886, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
