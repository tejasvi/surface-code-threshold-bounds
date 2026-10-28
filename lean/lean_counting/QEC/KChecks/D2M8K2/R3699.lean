import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14796 = true := by
  decide +kernel

theorem tot14796 : totK PD2M8K2 D2M8K2.t14796 = [0, 154859269859, 466250507541, 258543897667, 16694152682, 0, 0, 0] := by
  decide +kernel

theorem rows14797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14797 = true := by
  decide +kernel

theorem tot14797 : totK PD2M8K2 D2M8K2.t14797 = [0, 0, 322332353763, 519251857740, 75894648661, 0, 0, 0] := by
  decide +kernel

theorem rows14798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14798 = true := by
  decide +kernel

theorem tot14798 : totK PD2M8K2 D2M8K2.t14798 = [0, 161711873696, 412219165521, 277866719941, 66626832832, 1415142070, 0, 0] := by
  decide +kernel

theorem rows14799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14799 = true := by
  decide +kernel

theorem tot14799 : totK PD2M8K2 D2M8K2.t14799 = [0, 180835702393, 453154657352, 249595306504, 17761305995, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
