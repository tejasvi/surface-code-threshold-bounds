import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1260 = true := by
  decide +kernel

theorem tot1260 : totK PD2M8K2 D2M8K2.t1260 = [161294311188, 441718242089, 279087241424, 29524518019, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1261 = true := by
  decide +kernel

theorem tot1261 : totK PD2M8K2 D2M8K2.t1261 = [92931878008, 377942653801, 369050303183, 62979333397, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows1262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1262 = true := by
  decide +kernel

theorem tot1262 : totK PD2M8K2 D2M8K2.t1262 = [0, 238827179078, 493307405083, 154139373157, 3699256714, 0, 0, 0] := by
  decide +kernel

theorem rows1263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1263 = true := by
  decide +kernel

theorem tot1263 : totK PD2M8K2 D2M8K2.t1263 = [0, 190189180427, 462290919368, 217672798504, 17074942803, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
