import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15828 = true := by
  decide +kernel

theorem tot15828 : totK PD2M8K2 D2M8K2.t15828 = [0, 176768716745, 452269284615, 277208088407, 28874446489, 0, 0, 0] := by
  decide +kernel

theorem rows15829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15829 = true := by
  decide +kernel

theorem tot15829 : totK PD2M8K2 D2M8K2.t15829 = [0, 174022821214, 458888213108, 262307460341, 19243339461, 0, 0, 0] := by
  decide +kernel

theorem rows15830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15830 = true := by
  decide +kernel

theorem tot15830 : totK PD2M8K2 D2M8K2.t15830 = [0, 0, 238514205368, 500578496399, 158764647794, 4939195023, 0, 0] := by
  decide +kernel

theorem rows15831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15831 = true := by
  decide +kernel

theorem tot15831 : totK PD2M8K2 D2M8K2.t15831 = [0, 0, 178853234700, 466258401670, 225485172601, 12790473784, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
