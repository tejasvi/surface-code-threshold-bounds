import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7228 = true := by
  decide +kernel

theorem tot7228 : totK PD2M8K2 D2M8K2.t7228 = [0, 0, 0, 262773124350, 494835432844, 123759994324, 2304167554, 0] := by
  decide +kernel

theorem rows7229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7229 = true := by
  decide +kernel

theorem tot7229 : totK PD2M8K2 D2M8K2.t7229 = [0, 0, 0, 244019434697, 466793219912, 155670399247, 11483332778, 0] := by
  decide +kernel

theorem rows7230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7230 = true := by
  decide +kernel

theorem tot7230 : totK PD2M8K2 D2M8K2.t7230 = [0, 0, 0, 186953151541, 483963235910, 197004608558, 9610913563, 0] := by
  decide +kernel

theorem rows7231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7231 = true := by
  decide +kernel

theorem tot7231 : totK PD2M8K2 D2M8K2.t7231 = [0, 0, 0, 169518938464, 482239224782, 204137868122, 8826250517, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
