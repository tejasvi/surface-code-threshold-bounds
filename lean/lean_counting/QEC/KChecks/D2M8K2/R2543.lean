import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10172 = true := by
  decide +kernel

theorem tot10172 : totK PD2M8K2 D2M8K2.t10172 = [0, 174324890571, 440308649769, 266640760241, 20183211654, 0, 0, 0] := by
  decide +kernel

theorem rows10173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10173 = true := by
  decide +kernel

theorem tot10173 : totK PD2M8K2 D2M8K2.t10173 = [0, 93768764846, 385160180162, 365420128056, 62689845689, 1268739303, 0, 0] := by
  decide +kernel

theorem rows10174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10174 = true := by
  decide +kernel

theorem tot10174 : totK PD2M8K2 D2M8K2.t10174 = [0, 0, 237257002764, 494984430670, 155453147203, 3699256714, 0, 0] := by
  decide +kernel

theorem rows10175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10175 = true := by
  decide +kernel

theorem tot10175 : totK PD2M8K2 D2M8K2.t10175 = [0, 0, 185674598115, 463193996425, 216821581705, 17080783126, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
