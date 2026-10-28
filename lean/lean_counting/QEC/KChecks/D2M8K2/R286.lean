import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1144 = true := by
  decide +kernel

theorem tot1144 : totK PD2M8K2 D2M8K2.t1144 = [0, 0, 236586104437, 499438014346, 151758089408, 3724448267, 0, 0] := by
  decide +kernel

theorem rows1145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1145 = true := by
  decide +kernel

theorem tot1145 : totK PD2M8K2 D2M8K2.t1145 = [0, 189010360964, 460503372424, 222557344928, 17182251135, 0, 0, 0] := by
  decide +kernel

theorem rows1146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1146 = true := by
  decide +kernel

theorem tot1146 : totK PD2M8K2 D2M8K2.t1146 = [0, 189790273525, 473707145334, 217924163709, 12534051746, 0, 0, 0] := by
  decide +kernel

theorem rows1147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1147 = true := by
  decide +kernel

theorem tot1147 : totK PD2M8K2 D2M8K2.t1147 = [0, 31975145486, 305033408293, 435215531098, 87463609813, 1326647619, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
