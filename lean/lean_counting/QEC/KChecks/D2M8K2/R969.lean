import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3876 = true := by
  decide +kernel

theorem tot3876 : totK PD2M8K2 D2M8K2.t3876 = [0, 87804909821, 367423432226, 368630636844, 62729462042, 1198073392, 0, 0] := by
  decide +kernel

theorem rows3877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3877 = true := by
  decide +kernel

theorem tot3877 : totK PD2M8K2 D2M8K2.t3877 = [0, 0, 247575486745, 501634682369, 139394557858, 4030866388, 0, 0] := by
  decide +kernel

theorem rows3878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3878 = true := by
  decide +kernel

theorem tot3878 : totK PD2M8K2 D2M8K2.t3878 = [0, 161053378024, 441882576153, 273370841638, 36175172662, 0, 0, 0] := by
  decide +kernel

theorem rows3879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3879 = true := by
  decide +kernel

theorem tot3879 : totK PD2M8K2 D2M8K2.t3879 = [0, 172699395268, 447547128737, 254423418775, 18885589135, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
