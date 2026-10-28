import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1796 = true := by
  decide +kernel

theorem tot1796 : totK PD2M8K2 D2M8K2.t1796 = [0, 0, 198925250132, 475488476401, 213794036413, 14707859566, 0, 0] := by
  decide +kernel

theorem rows1797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1797 = true := by
  decide +kernel

theorem tot1797 : totK PD2M8K2 D2M8K2.t1797 = [0, 0, 168962645644, 455697853731, 228412993811, 16632994142, 0, 0] := by
  decide +kernel

theorem rows1798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1798 = true := by
  decide +kernel

theorem tot1798 : totK PD2M8K2 D2M8K2.t1798 = [0, 0, 87476419814, 377610381899, 340011422394, 62902528491, 1369150432, 0] := by
  decide +kernel

theorem rows1799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1799 = true := by
  decide +kernel

theorem tot1799 : totK PD2M8K2 D2M8K2.t1799 = [0, 0, 0, 319243685559, 457824128552, 75544887691, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
