import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15324 = true := by
  decide +kernel

theorem tot15324 : totK PD2M8K2 D2M8K2.t15324 = [0, 0, 173127692068, 457028983482, 270942656607, 32170542732, 0, 0] := by
  decide +kernel

theorem rows15325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15325 = true := by
  decide +kernel

theorem tot15325 : totK PD2M8K2 D2M8K2.t15325 = [0, 0, 175061879071, 445932527453, 268047421216, 19089918572, 0, 0] := by
  decide +kernel

theorem rows15326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15326 = true := by
  decide +kernel

theorem tot15326 : totK PD2M8K2 D2M8K2.t15326 = [0, 0, 93773531552, 392190649610, 368259117738, 58010433020, 1249641317, 0] := by
  decide +kernel

theorem rows15327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15327 = true := by
  decide +kernel

theorem tot15327 : totK PD2M8K2 D2M8K2.t15327 = [0, 0, 0, 237583642457, 500245209623, 148052097179, 3633193399, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
