import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14952 = true := by
  decide +kernel

theorem tot14952 : totK PD2M8K2 D2M8K2.t14952 = [0, 189843216251, 469342534221, 250016970679, 23323474648, 0, 0, 0] := by
  decide +kernel

theorem rows14953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14953 = true := by
  decide +kernel

theorem tot14953 : totK PD2M8K2 D2M8K2.t14953 = [0, 165652694606, 474684771056, 244093221197, 12412960461, 0, 0, 0] := by
  decide +kernel

theorem rows14954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14954 = true := by
  decide +kernel

theorem tot14954 : totK PD2M8K2 D2M8K2.t14954 = [0, 0, 284382503738, 501614246797, 114038333977, 1161838861, 0, 0] := by
  decide +kernel

theorem rows14955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14955 = true := by
  decide +kernel

theorem tot14955 : totK PD2M8K2 D2M8K2.t14955 = [0, 37947253655, 222496615903, 439799832627, 173771003324, 8017150856, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
