import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4068 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4068 = true := by
  decide +kernel

theorem tot4068 : totK PA10K2 A10K2.t4068 = [0, 0, 581144644929, 1986337355461, 1916766920553, 471572617947, 25814882083, 0, 0, 0] := by
  decide +kernel

theorem rows4069 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4069 = true := by
  decide +kernel

theorem tot4069 : totK PA10K2 A10K2.t4069 = [0, 0, 0, 747979116325, 2149786507637, 1676278736847, 347355480934, 12219140272, 0, 0] := by
  decide +kernel

theorem rows4070 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4070 = true := by
  decide +kernel

theorem tot4070 : totK PA10K2 A10K2.t4070 = [0, 0, 277605137434, 1255510164487, 2032208960573, 1230804992835, 145880919807, 0, 0, 0] := by
  decide +kernel

theorem rows4071 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4071 = true := by
  decide +kernel

theorem tot4071 : totK PA10K2 A10K2.t4071 = [0, 0, 613737279027, 2015161385932, 1905688394132, 467811472988, 16972980469, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
