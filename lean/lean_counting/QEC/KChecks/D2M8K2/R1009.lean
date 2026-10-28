import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4036 = true := by
  decide +kernel

theorem tot4036 : totK PD2M8K2 D2M8K2.t4036 = [0, 0, 182755373684, 465946772131, 229566815334, 16524485653, 0, 0] := by
  decide +kernel

theorem rows4037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4037 = true := by
  decide +kernel

theorem tot4037 : totK PD2M8K2 D2M8K2.t4037 = [0, 0, 177283793468, 444842632225, 275496986369, 28496840222, 0, 0] := by
  decide +kernel

theorem rows4038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4038 = true := by
  decide +kernel

theorem tot4038 : totK PD2M8K2 D2M8K2.t4038 = [0, 0, 194918570766, 488708416544, 226493263549, 8977779328, 0, 0] := by
  decide +kernel

theorem rows4039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4039 = true := by
  decide +kernel

theorem tot4039 : totK PD2M8K2 D2M8K2.t4039 = [0, 0, 37647871296, 280501625924, 401811676491, 178217337610, 21385604922, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
