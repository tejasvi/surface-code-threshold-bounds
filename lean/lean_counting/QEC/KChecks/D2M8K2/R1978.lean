import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7912 = true := by
  decide +kernel

theorem tot7912 : totK PD2M8K2 D2M8K2.t7912 = [0, 111352719478, 387026230955, 371435887391, 48350304330, 0, 0, 0] := by
  decide +kernel

theorem rows7913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7913 = true := by
  decide +kernel

theorem tot7913 : totK PD2M8K2 D2M8K2.t7913 = [0, 183868046121, 458845101978, 236004166773, 16971693599, 0, 0, 0] := by
  decide +kernel

theorem rows7914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7914 = true := by
  decide +kernel

theorem tot7914 : totK PD2M8K2 D2M8K2.t7914 = [0, 123537675262, 438560955956, 318445569716, 34899526320, 0, 0, 0] := by
  decide +kernel

theorem rows7915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7915 = true := by
  decide +kernel

theorem tot7915 : totK PD2M8K2 D2M8K2.t7915 = [0, 0, 171896077427, 445683065054, 258086969929, 25127349078, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
