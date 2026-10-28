import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14132 = true := by
  decide +kernel

theorem tot14132 : totK PD2M8K2 D2M8K2.t14132 = [196801853833, 457625569569, 229950183320, 23184898492, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14133 = true := by
  decide +kernel

theorem tot14133 : totK PD2M8K2 D2M8K2.t14133 = [177799613222, 450746338570, 231130030764, 18185084111, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14134 = true := by
  decide +kernel

theorem tot14134 : totK PD2M8K2 D2M8K2.t14134 = [0, 303330632993, 487889171449, 91864177869, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows14135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14135 = true := by
  decide +kernel

theorem tot14135 : totK PD2M8K2 D2M8K2.t14135 = [87414637357, 318877417997, 368950626333, 102947558566, 3884009855, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
