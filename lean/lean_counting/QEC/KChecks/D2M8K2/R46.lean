import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t184 = true := by
  decide +kernel

theorem tot184 : totK PD2M8K2 D2M8K2.t184 = [0, 167123509284, 456280692175, 248200907460, 18832117332, 0, 0, 0] := by
  decide +kernel

theorem rows185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t185 = true := by
  decide +kernel

theorem tot185 : totK PD2M8K2 D2M8K2.t185 = [0, 0, 225166477584, 500794279950, 149521376977, 7149690752, 0, 0] := by
  decide +kernel

theorem rows186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t186 = true := by
  decide +kernel

theorem tot186 : totK PD2M8K2 D2M8K2.t186 = [0, 87770539582, 292946109911, 371039142968, 113038977880, 5942689053, 0, 0] := by
  decide +kernel

theorem rows187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t187 = true := by
  decide +kernel

theorem tot187 : totK PD2M8K2 D2M8K2.t187 = [0, 151573637781, 456751826208, 263618338454, 15760345138, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
