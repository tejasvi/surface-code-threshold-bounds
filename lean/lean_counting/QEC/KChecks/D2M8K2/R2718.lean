import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10872 = true := by
  decide +kernel

theorem tot10872 : totK PD2M8K2 D2M8K2.t10872 = [0, 74089972484, 312285059204, 363860386236, 150718995863, 16947379154, 0, 0] := by
  decide +kernel

theorem rows10873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10873 = true := by
  decide +kernel

theorem tot10873 : totK PD2M8K2 D2M8K2.t10873 = [0, 0, 200850714016, 473105478946, 220274099745, 10864167075, 0, 0] := by
  decide +kernel

theorem rows10874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10874 = true := by
  decide +kernel

theorem tot10874 : totK PD2M8K2 D2M8K2.t10874 = [0, 86101696324, 250130081669, 375331976477, 179828292239, 8209296672, 0, 0] := by
  decide +kernel

theorem rows10875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10875 = true := by
  decide +kernel

theorem tot10875 : totK PD2M8K2 D2M8K2.t10875 = [0, 182440129311, 471209006761, 254448201377, 23042648846, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
