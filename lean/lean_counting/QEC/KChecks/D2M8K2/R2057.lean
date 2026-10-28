import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8228 = true := by
  decide +kernel

theorem tot8228 : totK PD2M8K2 D2M8K2.t8228 = [0, 243994416245, 489159604561, 158118584673, 8470662040, 0, 0, 0] := by
  decide +kernel

theorem rows8229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8229 = true := by
  decide +kernel

theorem tot8229 : totK PD2M8K2 D2M8K2.t8229 = [124695669297, 358991992143, 308623134387, 87442329338, 3581949829, 0, 0, 0] := by
  decide +kernel

theorem rows8230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8230 = true := by
  decide +kernel

theorem tot8230 : totK PD2M8K2 D2M8K2.t8230 = [183912478252, 434416754424, 238278739630, 23762901354, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8231 = true := by
  decide +kernel

theorem tot8231 : totK PD2M8K2 D2M8K2.t8231 = [105614364164, 429112623389, 330694313746, 27783303540, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
