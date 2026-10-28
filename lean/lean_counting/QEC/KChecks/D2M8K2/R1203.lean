import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4812 = true := by
  decide +kernel

theorem tot4812 : totK PD2M8K2 D2M8K2.t4812 = [0, 0, 153096016067, 451351884516, 285035351451, 28418548751, 0, 0] := by
  decide +kernel

theorem rows4813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4813 = true := by
  decide +kernel

theorem tot4813 : totK PD2M8K2 D2M8K2.t4813 = [0, 0, 176193132134, 451961500357, 265890672568, 19238080613, 0, 0] := by
  decide +kernel

theorem rows4814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4814 = true := by
  decide +kernel

theorem tot4814 : totK PD2M8K2 D2M8K2.t4814 = [0, 0, 0, 304526713817, 497707269909, 94551401083, 1435164049, 0] := by
  decide +kernel

theorem rows4815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4815 = true := by
  decide +kernel

theorem tot4815 : totK PD2M8K2 D2M8K2.t4815 = [0, 0, 170769880466, 448850490610, 256734354410, 24861371257, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
