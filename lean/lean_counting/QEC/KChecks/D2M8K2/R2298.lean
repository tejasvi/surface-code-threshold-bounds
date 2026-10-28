import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9192 = true := by
  decide +kernel

theorem tot9192 : totK PD2M8K2 D2M8K2.t9192 = [157810339304, 399932983116, 278821000212, 73195479194, 3455941720, 0, 0, 0] := by
  decide +kernel

theorem rows9193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9193 = true := by
  decide +kernel

theorem tot9193 : totK PD2M8K2 D2M8K2.t9193 = [177860025660, 432243069216, 274448780564, 30619655124, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9194 = true := by
  decide +kernel

theorem tot9194 : totK PD2M8K2 D2M8K2.t9194 = [80722692060, 365711634387, 372400561942, 71046578110, 1197396724, 0, 0, 0] := by
  decide +kernel

theorem rows9195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9195 = true := by
  decide +kernel

theorem tot9195 : totK PD2M8K2 D2M8K2.t9195 = [0, 262535623419, 484515364659, 152037113079, 8464368736, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
