import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4896 = true := by
  decide +kernel

theorem tot4896 : totK PD2M8K2 D2M8K2.t4896 = [0, 0, 188194659600, 464904687267, 246184439519, 18376726353, 0, 0] := by
  decide +kernel

theorem rows4897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4897 = true := by
  decide +kernel

theorem tot4897 : totK PD2M8K2 D2M8K2.t4897 = [0, 0, 30487714703, 379590988116, 448744876820, 48056133392, 0, 0] := by
  decide +kernel

theorem rows4898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4898 = true := by
  decide +kernel

theorem tot4898 : totK PD2M8K2 D2M8K2.t4898 = [0, 0, 152128849644, 374704890563, 294284156861, 62573269291, 1288481286, 0] := by
  decide +kernel

theorem rows4899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4899 = true := by
  decide +kernel

theorem tot4899 : totK PD2M8K2 D2M8K2.t4899 = [0, 0, 160599878095, 444836019898, 281182227694, 29976125450, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
