import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14048 = true := by
  decide +kernel

theorem tot14048 : totK PD2M8K2 D2M8K2.t14048 = [0, 0, 190851356943, 479130555488, 217887469745, 10660803951, 0, 0] := by
  decide +kernel

theorem rows14049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14049 = true := by
  decide +kernel

theorem tot14049 : totK PD2M8K2 D2M8K2.t14049 = [0, 0, 166441867172, 457450308523, 242079369468, 13293272603, 0, 0] := by
  decide +kernel

theorem rows14050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14050 = true := by
  decide +kernel

theorem tot14050 : totK PD2M8K2 D2M8K2.t14050 = [0, 0, 182210025958, 457751809595, 261191146702, 23136226215, 0, 0] := by
  decide +kernel

theorem rows14051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14051 = true := by
  decide +kernel

theorem tot14051 : totK PD2M8K2 D2M8K2.t14051 = [0, 0, 170066474192, 456346287795, 236828464967, 10129403048, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
