import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4724 = true := by
  decide +kernel

theorem tot4724 : totK PD2M8K2 D2M8K2.t4724 = [0, 0, 211109055118, 496806567827, 195076314959, 5430665091, 0, 0] := by
  decide +kernel

theorem rows4725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4725 = true := by
  decide +kernel

theorem tot4725 : totK PD2M8K2 D2M8K2.t4725 = [0, 167885818788, 374723630282, 254699535990, 102168966587, 6775760191, 0, 0] := by
  decide +kernel

theorem rows4726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4726 = true := by
  decide +kernel

theorem tot4726 : totK PD2M8K2 D2M8K2.t4726 = [0, 170303095835, 441480150273, 285713778486, 30360088343, 0, 0, 0] := by
  decide +kernel

theorem rows4727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4727 = true := by
  decide +kernel

theorem tot4727 : totK PD2M8K2 D2M8K2.t4727 = [0, 107837199678, 440066299762, 330366515828, 27558554489, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
