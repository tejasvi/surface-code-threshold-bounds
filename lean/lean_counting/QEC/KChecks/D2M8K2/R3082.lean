import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12328 = true := by
  decide +kernel

theorem tot12328 : totK PD2M8K2 D2M8K2.t12328 = [177502607452, 469293700745, 259280507518, 23157714906, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12329 = true := by
  decide +kernel

theorem tot12329 : totK PD2M8K2 D2M8K2.t12329 = [181056272621, 459846957455, 248362401966, 18185084111, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12330 = true := by
  decide +kernel

theorem tot12330 : totK PD2M8K2 D2M8K2.t12330 = [0, 314272266417, 498622268486, 94479336542, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows12331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12331 = true := by
  decide +kernel

theorem tot12331 : totK PD2M8K2 D2M8K2.t12331 = [0, 269487799592, 506207379626, 125744035860, 3884009855, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
