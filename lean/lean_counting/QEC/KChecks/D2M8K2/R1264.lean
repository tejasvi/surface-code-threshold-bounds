import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5056 = true := by
  decide +kernel

theorem tot5056 : totK PD2M8K2 D2M8K2.t5056 = [0, 0, 188171967692, 471819011017, 206173104785, 10794973564, 0, 0] := by
  decide +kernel

theorem rows5057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5057 = true := by
  decide +kernel

theorem tot5057 : totK PD2M8K2 D2M8K2.t5057 = [0, 0, 65463062829, 352915958923, 375368277684, 61530674257, 1239866073, 0] := by
  decide +kernel

theorem rows5058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5058 = true := by
  decide +kernel

theorem tot5058 : totK PD2M8K2 D2M8K2.t5058 = [0, 0, 92785537557, 383945928931, 380759258966, 38408447872, 0, 0] := by
  decide +kernel

theorem rows5059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5059 = true := by
  decide +kernel

theorem tot5059 : totK PD2M8K2 D2M8K2.t5059 = [0, 0, 158546736650, 452666481379, 288422376746, 27148564577, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
