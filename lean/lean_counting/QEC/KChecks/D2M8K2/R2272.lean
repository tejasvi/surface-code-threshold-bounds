import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9088 = true := by
  decide +kernel

theorem tot9088 : totK PD2M8K2 D2M8K2.t9088 = [0, 0, 0, 300194490452, 459669243528, 81601654993, 1217496766, 0] := by
  decide +kernel

theorem rows9089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9089 = true := by
  decide +kernel

theorem tot9089 : totK PD2M8K2 D2M8K2.t9089 = [0, 0, 244877256704, 457261211907, 198957732172, 19989377505, 0, 0] := by
  decide +kernel

theorem rows9090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9090 = true := by
  decide +kernel

theorem tot9090 : totK PD2M8K2 D2M8K2.t9090 = [0, 0, 171065875030, 505599380750, 208546278464, 8031208919, 0, 0] := by
  decide +kernel

theorem rows9091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9091 = true := by
  decide +kernel

theorem tot9091 : totK PD2M8K2 D2M8K2.t9091 = [0, 0, 173395879649, 461174940935, 241121944565, 20963427163, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
