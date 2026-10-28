import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15500 = true := by
  decide +kernel

theorem tot15500 : totK PD2M8K2 D2M8K2.t15500 = [0, 0, 194047914884, 472230102352, 227868468712, 12503027455, 0, 0] := by
  decide +kernel

theorem rows15501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15501 = true := by
  decide +kernel

theorem tot15501 : totK PD2M8K2 D2M8K2.t15501 = [0, 0, 19735703396, 316469788308, 459833324579, 96585004420, 1242138600, 0] := by
  decide +kernel

theorem rows15502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15502 = true := by
  decide +kernel

theorem tot15502 : totK PD2M8K2 D2M8K2.t15502 = [0, 0, 0, 207975154274, 474760700916, 167444789638, 7182288656, 0] := by
  decide +kernel

theorem rows15503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15503 = true := by
  decide +kernel

theorem tot15503 : totK PD2M8K2 D2M8K2.t15503 = [0, 161564142879, 328561995991, 135174777785, 148074409370, 116750672292, 13326740810, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
