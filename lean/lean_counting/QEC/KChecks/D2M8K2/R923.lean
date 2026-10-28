import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3692 = true := by
  decide +kernel

theorem tot3692 : totK PD2M8K2 D2M8K2.t3692 = [163689140280, 451725018609, 250678507400, 18197172049, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3693 = true := by
  decide +kernel

theorem tot3693 : totK PD2M8K2 D2M8K2.t3693 = [88680480173, 370872758838, 369242846671, 72967189765, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows3694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3694 = true := by
  decide +kernel

theorem tot3694 : totK PD2M8K2 D2M8K2.t3694 = [0, 308304054244, 516253788752, 76077126158, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3695 = true := by
  decide +kernel

theorem tot3695 : totK PD2M8K2 D2M8K2.t3695 = [186800965232, 448783693926, 245534558998, 27476823083, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
