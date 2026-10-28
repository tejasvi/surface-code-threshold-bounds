import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14200 = true := by
  decide +kernel

theorem tot14200 : totK PD2M8K2 D2M8K2.t14200 = [183994015272, 466479928127, 255697149815, 23124774842, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14201 = true := by
  decide +kernel

theorem tot14201 : totK PD2M8K2 D2M8K2.t14201 = [186803805358, 478919886709, 225489197514, 12373752831, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14202 = true := by
  decide +kernel

theorem tot14202 : totK PD2M8K2 D2M8K2.t14202 = [33828699371, 316961441467, 459259569033, 94226517927, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows14203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14203 = true := by
  decide +kernel

theorem tot14203 : totK PD2M8K2 D2M8K2.t14203 = [0, 199605901993, 476526811496, 189268515262, 11885407614, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
