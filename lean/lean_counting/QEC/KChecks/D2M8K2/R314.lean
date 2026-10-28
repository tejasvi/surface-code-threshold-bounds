import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1256 = true := by
  decide +kernel

theorem tot1256 : totK PD2M8K2 D2M8K2.t1256 = [151572336400, 434279883441, 296805994062, 39057548703, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1257 = true := by
  decide +kernel

theorem tot1257 : totK PD2M8K2 D2M8K2.t1257 = [174748793687, 462219076383, 242645182823, 16597298387, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1258 = true := by
  decide +kernel

theorem tot1258 : totK PD2M8K2 D2M8K2.t1258 = [0, 275211467931, 514355115853, 105278560085, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows1259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1259 = true := by
  decide +kernel

theorem tot1259 : totK PD2M8K2 D2M8K2.t1259 = [172161542757, 393710486010, 243508018134, 77329370401, 3884009855, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
