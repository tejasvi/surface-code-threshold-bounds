import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15352 = true := by
  decide +kernel

theorem tot15352 : totK PD2M8K2 D2M8K2.t15352 = [0, 0, 75203464672, 317391501001, 364560124831, 152484690866, 17176948997, 0] := by
  decide +kernel

theorem rows15353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15353 = true := by
  decide +kernel

theorem tot15353 : totK PD2M8K2 D2M8K2.t15353 = [0, 0, 0, 206287101500, 466078578364, 204509937164, 11867500000, 0] := by
  decide +kernel

theorem rows15354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15354 = true := by
  decide +kernel

theorem tot15354 : totK PD2M8K2 D2M8K2.t15354 = [0, 0, 61082895301, 221998497615, 408925616415, 183862499443, 7877424857, 0] := by
  decide +kernel

theorem rows15355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15355 = true := by
  decide +kernel

theorem tot15355 : totK PD2M8K2 D2M8K2.t15355 = [0, 0, 186298867753, 468626083590, 247424048228, 23099921452, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
