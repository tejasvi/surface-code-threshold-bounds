import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4756 = true := by
  decide +kernel

theorem tot4756 : totK PD2M8K2 D2M8K2.t4756 = [0, 0, 271648604978, 514058765177, 103198085646, 1369150432, 0, 0] := by
  decide +kernel

theorem rows4757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4757 = true := by
  decide +kernel

theorem tot4757 : totK PD2M8K2 D2M8K2.t4757 = [0, 136979003893, 397244771975, 343936040761, 44183826445, 0, 0, 0] := by
  decide +kernel

theorem rows4758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4758 = true := by
  decide +kernel

theorem tot4758 : totK PD2M8K2 D2M8K2.t4758 = [0, 189526998551, 470658365458, 232670207147, 15795520027, 0, 0, 0] := by
  decide +kernel

theorem rows4759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4759 = true := by
  decide +kernel

theorem tot4759 : totK PD2M8K2 D2M8K2.t4759 = [0, 89480556010, 407874313458, 360471752776, 66800118940, 5319205844, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
