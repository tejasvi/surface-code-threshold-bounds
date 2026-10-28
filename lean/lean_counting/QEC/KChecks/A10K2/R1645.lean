import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6580 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6580 = true := by
  decide +kernel

theorem tot6580 : totK PA10K2 A10K2.t6580 = [0, 0, 152814207430, 945117361214, 2000799241644, 1282995400749, 239904770714, 6354482628, 0, 0] := by
  decide +kernel

theorem rows6581 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6581 = true := by
  decide +kernel

theorem tot6581 : totK PA10K2 A10K2.t6581 = [0, 0, 430645959760, 1771557370096, 1998403111109, 542051654549, 26491486257, 0, 0, 0] := by
  decide +kernel

theorem rows6582 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6582 = true := by
  decide +kernel

theorem tot6582 : totK PA10K2 A10K2.t6582 = [0, 0, 258566662976, 1266955300700, 2078880442018, 1162940544426, 142063480280, 0, 0, 0] := by
  decide +kernel

theorem rows6583 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6583 = true := by
  decide +kernel

theorem tot6583 : totK PA10K2 A10K2.t6583 = [0, 0, 73678395671, 630796734124, 1838867255789, 1692203140159, 435368714482, 31452573850, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
