import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4828 = true := by
  decide +kernel

theorem tot4828 : totK PD2M8K2 D2M8K2.t4828 = [0, 0, 189533014415, 470964970215, 221073410566, 12523541424, 0, 0] := by
  decide +kernel

theorem rows4829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4829 = true := by
  decide +kernel

theorem tot4829 : totK PD2M8K2 D2M8K2.t4829 = [0, 0, 153671077068, 461556132471, 259650261869, 15552237960, 0, 0] := by
  decide +kernel

theorem rows4830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4830 = true := by
  decide +kernel

theorem tot4830 : totK PD2M8K2 D2M8K2.t4830 = [0, 0, 188790040371, 444135546318, 232494267359, 16299775508, 0, 0] := by
  decide +kernel

theorem rows4831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4831 = true := by
  decide +kernel

theorem tot4831 : totK PD2M8K2 D2M8K2.t4831 = [0, 0, 54666102996, 354337156978, 393924808004, 60686591848, 1096505104, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
