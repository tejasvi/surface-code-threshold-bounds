import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6116 = true := by
  decide +kernel

theorem tot6116 : totK PD2M8K2 D2M8K2.t6116 = [0, 0, 176923905066, 438147640685, 266726222434, 25113949685, 0, 0] := by
  decide +kernel

theorem rows6117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6117 = true := by
  decide +kernel

theorem tot6117 : totK PD2M8K2 D2M8K2.t6117 = [0, 0, 141341601695, 453247244997, 290166536819, 17904341613, 0, 0] := by
  decide +kernel

theorem rows6118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6118 = true := by
  decide +kernel

theorem tot6118 : totK PD2M8K2 D2M8K2.t6118 = [0, 0, 18114697088, 294954555934, 473579958890, 94167986076, 1332468113, 0] := by
  decide +kernel

theorem rows6119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6119 = true := by
  decide +kernel

theorem tot6119 : totK PD2M8K2 D2M8K2.t6119 = [0, 0, 186040482912, 464289194036, 239599519665, 20063464395, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
