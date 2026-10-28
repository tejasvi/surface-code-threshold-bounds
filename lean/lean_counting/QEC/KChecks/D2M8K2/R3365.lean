import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13460 = true := by
  decide +kernel

theorem tot13460 : totK PD2M8K2 D2M8K2.t13460 = [0, 0, 181156563603, 478229724709, 247370722922, 17374191222, 0, 0] := by
  decide +kernel

theorem rows13461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13461 = true := by
  decide +kernel

theorem tot13461 : totK PD2M8K2 D2M8K2.t13461 = [0, 0, 189710791265, 476113503950, 229078695824, 12523541424, 0, 0] := by
  decide +kernel

theorem rows13462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13462 = true := by
  decide +kernel

theorem tot13462 : totK PD2M8K2 D2M8K2.t13462 = [0, 0, 0, 289630391750, 490351352439, 93623805102, 1178750802, 0] := by
  decide +kernel

theorem rows13463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13463 = true := by
  decide +kernel

theorem tot13463 : totK PD2M8K2 D2M8K2.t13463 = [0, 0, 0, 216118364281, 471259092890, 177904192083, 11991925116, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
