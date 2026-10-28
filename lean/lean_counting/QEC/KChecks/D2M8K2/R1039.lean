import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4156 = true := by
  decide +kernel

theorem tot4156 : totK PD2M8K2 D2M8K2.t4156 = [0, 0, 186590644655, 471023675400, 227119412586, 15844255384, 0, 0] := by
  decide +kernel

theorem rows4157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4157 = true := by
  decide +kernel

theorem tot4157 : totK PD2M8K2 D2M8K2.t4157 = [0, 0, 194227280568, 455898430885, 221848972886, 16702988424, 0, 0] := by
  decide +kernel

theorem rows4158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4158 = true := by
  decide +kernel

theorem tot4158 : totK PD2M8K2 D2M8K2.t4158 = [0, 0, 56013666367, 363733367585, 396138789478, 58996994384, 0, 0] := by
  decide +kernel

theorem rows4159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4159 = true := by
  decide +kernel

theorem tot4159 : totK PD2M8K2 D2M8K2.t4159 = [0, 28842453189, 34147035210, 251942122951, 440146520573, 117775215144, 2586295899, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
