import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9024 = true := by
  decide +kernel

theorem tot9024 : totK PD2M8K2 D2M8K2.t9024 = [0, 0, 229290491037, 484450307691, 166580940959, 8470662040, 0, 0] := by
  decide +kernel

theorem rows9025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9025 = true := by
  decide +kernel

theorem tot9025 : totK PD2M8K2 D2M8K2.t9025 = [0, 105938297661, 349096294373, 343592574378, 88236264829, 3521263076, 0, 0] := by
  decide +kernel

theorem rows9026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9026 = true := by
  decide +kernel

theorem tot9026 : totK PD2M8K2 D2M8K2.t9026 = [0, 192762923542, 429567802746, 232749658960, 19461616802, 0, 0, 0] := by
  decide +kernel

theorem rows9027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9027 = true := by
  decide +kernel

theorem tot9027 : totK PD2M8K2 D2M8K2.t9027 = [0, 109054830415, 438255902611, 313683466073, 26427017039, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
