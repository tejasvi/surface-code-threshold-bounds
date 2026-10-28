import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6964 = true := by
  decide +kernel

theorem tot6964 : totK PD2M8K2 D2M8K2.t6964 = [0, 190676476894, 469300731043, 247345351429, 18380633500, 0, 0, 0] := by
  decide +kernel

theorem rows6965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6965 = true := by
  decide +kernel

theorem tot6965 : totK PD2M8K2 D2M8K2.t6965 = [0, 33204691154, 332069184867, 440500416536, 74856786520, 1062926506, 0, 0] := by
  decide +kernel

theorem rows6966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6966 = true := by
  decide +kernel

theorem tot6966 : totK PD2M8K2 D2M8K2.t6966 = [0, 84824948312, 326478623623, 376149974664, 91148330153, 3720136285, 0, 0] := by
  decide +kernel

theorem rows6967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6967 = true := by
  decide +kernel

theorem tot6967 : totK PD2M8K2 D2M8K2.t6967 = [0, 177936335313, 460737136217, 261117844697, 23709942808, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
