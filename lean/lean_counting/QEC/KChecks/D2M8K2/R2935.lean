import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11740 = true := by
  decide +kernel

theorem tot11740 : totK PD2M8K2 D2M8K2.t11740 = [0, 33248694457, 313980683461, 447271706345, 87111736884, 1198073392, 0, 0] := by
  decide +kernel

theorem rows11741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11741 = true := by
  decide +kernel

theorem tot11741 : totK PD2M8K2 D2M8K2.t11741 = [0, 137672207893, 431228537293, 305605589205, 27383449672, 0, 0, 0] := by
  decide +kernel

theorem rows11742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11742 = true := by
  decide +kernel

theorem tot11742 : totK PD2M8K2 D2M8K2.t11742 = [0, 179362876163, 446483784909, 247666920442, 19515985933, 0, 0, 0] := by
  decide +kernel

theorem rows11743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11743 = true := by
  decide +kernel

theorem tot11743 : totK PD2M8K2 D2M8K2.t11743 = [0, 90561473391, 377809621367, 349633344526, 54284512026, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
