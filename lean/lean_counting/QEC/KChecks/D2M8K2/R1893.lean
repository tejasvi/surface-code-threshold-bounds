import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7572 = true := by
  decide +kernel

theorem tot7572 : totK PD2M8K2 D2M8K2.t7572 = [0, 0, 182589323308, 472820134632, 248452841664, 17256164024, 0, 0] := by
  decide +kernel

theorem rows7573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7573 = true := by
  decide +kernel

theorem tot7573 : totK PD2M8K2 D2M8K2.t7573 = [0, 0, 175521683754, 479713552413, 230049699481, 12237612490, 0, 0] := by
  decide +kernel

theorem rows7574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7574 = true := by
  decide +kernel

theorem tot7574 : totK PD2M8K2 D2M8K2.t7574 = [0, 0, 0, 290082156371, 485748142446, 100285677285, 1162935789, 0] := by
  decide +kernel

theorem rows7575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7575 = true := by
  decide +kernel

theorem tot7575 : totK PD2M8K2 D2M8K2.t7575 = [0, 0, 36272210802, 209271521435, 417540485723, 178578018167, 11853261585, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
