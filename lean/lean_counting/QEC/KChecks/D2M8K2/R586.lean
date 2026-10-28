import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2344 = true := by
  decide +kernel

theorem tot2344 : totK PD2M8K2 D2M8K2.t2344 = [0, 199366794800, 474244537204, 221753153693, 12749351102, 0, 0, 0] := by
  decide +kernel

theorem rows2345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2345 = true := by
  decide +kernel

theorem tot2345 : totK PD2M8K2 D2M8K2.t2345 = [0, 3950786586, 318569003679, 469447094784, 91579377459, 1096505104, 0, 0] := by
  decide +kernel

theorem rows2346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2346 = true := by
  decide +kernel

theorem tot2346 : totK PD2M8K2 D2M8K2.t2346 = [0, 104893840773, 344899242182, 341726967792, 91160278917, 3884009855, 0, 0] := by
  decide +kernel

theorem rows2347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2347 = true := by
  decide +kernel

theorem tot2347 : totK PD2M8K2 D2M8K2.t2347 = [0, 166778826144, 439039947964, 272576371253, 29524518019, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
