import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15228 = true := by
  decide +kernel

theorem tot15228 : totK PD2M8K2 D2M8K2.t15228 = [0, 0, 92342479873, 274416808640, 337798343599, 168824352269, 15908383818, 0] := by
  decide +kernel

theorem rows15229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15229 = true := by
  decide +kernel

theorem tot15229 : totK PD2M8K2 D2M8K2.t15229 = [0, 0, 174846244669, 476325652920, 235242574413, 14566626306, 0, 0] := by
  decide +kernel

theorem rows15230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15230 = true := by
  decide +kernel

theorem tot15230 : totK PD2M8K2 D2M8K2.t15230 = [0, 0, 174317904896, 463238370475, 244790327389, 14330943302, 0, 0] := by
  decide +kernel

theorem rows15231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15231 = true := by
  decide +kernel

theorem tot15231 : totK PD2M8K2 D2M8K2.t15231 = [0, 0, 0, 281320941082, 508306105088, 111677681307, 1369150432, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
