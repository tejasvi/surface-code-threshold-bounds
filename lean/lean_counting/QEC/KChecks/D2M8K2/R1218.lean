import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4872 = true := by
  decide +kernel

theorem tot4872 : totK PD2M8K2 D2M8K2.t4872 = [0, 0, 182137505762, 474154942453, 250579823332, 16317612774, 0, 0] := by
  decide +kernel

theorem rows4873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4873 = true := by
  decide +kernel

theorem tot4873 : totK PD2M8K2 D2M8K2.t4873 = [0, 0, 0, 246574142147, 506086668489, 122659785463, 1268739303, 0] := by
  decide +kernel

theorem rows4874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4874 = true := by
  decide +kernel

theorem tot4874 : totK PD2M8K2 D2M8K2.t4874 = [0, 0, 0, 188219550797, 461668396006, 218175768774, 13844440804, 0] := by
  decide +kernel

theorem rows4875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4875 = true := by
  decide +kernel

theorem tot4875 : totK PD2M8K2 D2M8K2.t4875 = [0, 0, 0, 216914529800, 489604972274, 163408294247, 3559364470, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
