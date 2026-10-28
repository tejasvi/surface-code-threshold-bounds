import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2884 = true := by
  decide +kernel

theorem tot2884 : totK PD2M8K2 D2M8K2.t2884 = [0, 8225356785, 301849810497, 468026634571, 80013370751, 1206465782, 0, 0] := by
  decide +kernel

theorem rows2885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2885 = true := by
  decide +kernel

theorem tot2885 : totK PD2M8K2 D2M8K2.t2885 = [0, 174217537795, 450937253640, 267981394958, 29184232052, 0, 0, 0] := by
  decide +kernel

theorem rows2886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2886 = true := by
  decide +kernel

theorem tot2886 : totK PD2M8K2 D2M8K2.t2886 = [0, 217272775124, 492214451632, 198140899531, 6915473937, 0, 0, 0] := by
  decide +kernel

theorem rows2887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2887 = true := by
  decide +kernel

theorem tot2887 : totK PD2M8K2 D2M8K2.t2887 = [0, 196438952908, 472296815494, 215429648316, 12811402063, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
