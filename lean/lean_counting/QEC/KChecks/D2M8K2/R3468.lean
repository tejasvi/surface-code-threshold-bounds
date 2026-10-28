import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13872 = true := by
  decide +kernel

theorem tot13872 : totK PD2M8K2 D2M8K2.t13872 = [0, 173075485837, 458205815771, 242693647143, 19545646109, 0, 0, 0] := by
  decide +kernel

theorem rows13873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13873 = true := by
  decide +kernel

theorem tot13873 : totK PD2M8K2 D2M8K2.t13873 = [0, 151465676402, 451859567061, 269891526040, 17717922764, 0, 0, 0] := by
  decide +kernel

theorem rows13874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13874 = true := by
  decide +kernel

theorem tot13874 : totK PD2M8K2 D2M8K2.t13874 = [0, 19982995165, 288440829616, 473464684402, 92268063874, 1239866073, 0, 0] := by
  decide +kernel

theorem rows13875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13875 = true := by
  decide +kernel

theorem tot13875 : totK PD2M8K2 D2M8K2.t13875 = [0, 179486119284, 451333305377, 263310795546, 26012142351, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
