import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6348 = true := by
  decide +kernel

theorem tot6348 : totK PD2M8K2 D2M8K2.t6348 = [0, 191438351671, 470963253342, 246389326929, 23294130616, 0, 0, 0] := by
  decide +kernel

theorem rows6349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6349 = true := by
  decide +kernel

theorem tot6349 : totK PD2M8K2 D2M8K2.t6349 = [0, 190077870934, 470445225757, 231313215619, 13797612932, 0, 0, 0] := by
  decide +kernel

theorem rows6350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6350 = true := by
  decide +kernel

theorem tot6350 : totK PD2M8K2 D2M8K2.t6350 = [0, 0, 298144632186, 488812104899, 110447399885, 1231519631, 0, 0] := by
  decide +kernel

theorem rows6351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6351 = true := by
  decide +kernel

theorem tot6351 : totK PD2M8K2 D2M8K2.t6351 = [0, 0, 203429896957, 501258066198, 172874033260, 4985411465, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
