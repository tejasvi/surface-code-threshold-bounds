import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14516 = true := by
  decide +kernel

theorem tot14516 : totK PD2M8K2 D2M8K2.t14516 = [0, 182313016982, 460671843114, 231983172718, 17369122476, 0, 0, 0] := by
  decide +kernel

theorem rows14517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14517 = true := by
  decide +kernel

theorem tot14517 : totK PD2M8K2 D2M8K2.t14517 = [0, 176275518442, 481305244547, 214367117664, 9713690252, 0, 0, 0] := by
  decide +kernel

theorem rows14518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14518 = true := by
  decide +kernel

theorem tot14518 : totK PD2M8K2 D2M8K2.t14518 = [0, 144796516941, 447919064649, 263399820049, 15235215915, 0, 0, 0] := by
  decide +kernel

theorem rows14519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14519 = true := by
  decide +kernel

theorem tot14519 : totK PD2M8K2 D2M8K2.t14519 = [0, 0, 278561705647, 475901853598, 87748292188, 1239866073, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
