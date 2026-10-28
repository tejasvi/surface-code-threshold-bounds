import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11824 = true := by
  decide +kernel

theorem tot11824 : totK PD2M8K2 D2M8K2.t11824 = [0, 193180069485, 465260208371, 231799016242, 16301871217, 0, 0, 0] := by
  decide +kernel

theorem rows11825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11825 = true := by
  decide +kernel

theorem tot11825 : totK PD2M8K2 D2M8K2.t11825 = [0, 59100038662, 329564800578, 416284235564, 85242686288, 1164319620, 0, 0] := by
  decide +kernel

theorem rows11826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11826 = true := by
  decide +kernel

theorem tot11826 : totK PD2M8K2 D2M8K2.t11826 = [0, 0, 202784554740, 471962567754, 189072402404, 11885407614, 0, 0] := by
  decide +kernel

theorem rows11827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11827 = true := by
  decide +kernel

theorem tot11827 : totK PD2M8K2 D2M8K2.t11827 = [0, 165990908636, 453582191904, 265253993211, 24584202582, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
