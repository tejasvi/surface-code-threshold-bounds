import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4048 = true := by
  decide +kernel

theorem tot4048 : totK PD2M8K2 D2M8K2.t4048 = [0, 0, 0, 269975765799, 491884880766, 130373061430, 4031931762, 0] := by
  decide +kernel

theorem rows4049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4049 = true := by
  decide +kernel

theorem tot4049 : totK PD2M8K2 D2M8K2.t4049 = [0, 0, 135903802350, 365987643231, 313596316228, 68713470434, 1186940923, 0] := by
  decide +kernel

theorem rows4050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4050 = true := by
  decide +kernel

theorem tot4050 : totK PD2M8K2 D2M8K2.t4050 = [0, 0, 162027083615, 440132170387, 278822558159, 30058763714, 0, 0] := by
  decide +kernel

theorem rows4051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4051 = true := by
  decide +kernel

theorem tot4051 : totK PD2M8K2 D2M8K2.t4051 = [0, 0, 116626386365, 445520064307, 311284192278, 14518949241, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
