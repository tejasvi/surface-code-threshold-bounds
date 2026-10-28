import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4268 = true := by
  decide +kernel

theorem tot4268 : totK PD2M8K2 D2M8K2.t4268 = [0, 0, 0, 172691515111, 388404399168, 268637615409, 55321755245, 1225787871] := by
  decide +kernel

theorem rows4269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4269 = true := by
  decide +kernel

theorem tot4269 : totK PD2M8K2 D2M8K2.t4269 = [0, 0, 0, 225739565243, 484958543940, 188395103945, 5562671799, 0] := by
  decide +kernel

theorem rows4270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4270 = true := by
  decide +kernel

theorem tot4270 : totK PD2M8K2 D2M8K2.t4270 = [0, 0, 167886171802, 346333817781, 246122966524, 125682521454, 10051291645, 0] := by
  decide +kernel

theorem rows4271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4271 = true := by
  decide +kernel

theorem tot4271 : totK PD2M8K2 D2M8K2.t4271 = [0, 0, 153068369903, 474998508856, 251788992270, 14220004360, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
