import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3832 = true := by
  decide +kernel

theorem tot3832 : totK PD2M8K2 D2M8K2.t3832 = [177883144228, 466452636955, 243657355873, 16434953954, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3833 = true := by
  decide +kernel

theorem tot3833 : totK PD2M8K2 D2M8K2.t3833 = [123174868417, 445038360006, 325201426259, 36756091005, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3834 = true := by
  decide +kernel

theorem tot3834 : totK PD2M8K2 D2M8K2.t3834 = [0, 170782943436, 444380537017, 258655263813, 25320643661, 0, 0, 0] := by
  decide +kernel

theorem rows3835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3835 = true := by
  decide +kernel

theorem tot3835 : totK PD2M8K2 D2M8K2.t3835 = [0, 167150245853, 492628483720, 238355836821, 7764445519, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
