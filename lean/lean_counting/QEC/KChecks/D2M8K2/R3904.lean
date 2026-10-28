import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15616 = true := by
  decide +kernel

theorem tot15616 : totK PD2M8K2 D2M8K2.t15616 = [0, 0, 243801974343, 506759721241, 162990456273, 3973351865, 0, 0] := by
  decide +kernel

theorem rows15617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15617 = true := by
  decide +kernel

theorem tot15617 : totK PD2M8K2 D2M8K2.t15617 = [0, 164861873023, 402951968913, 268187847896, 68727159514, 1409560813, 0, 0] := by
  decide +kernel

theorem rows15618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15618 = true := by
  decide +kernel

theorem tot15618 : totK PD2M8K2 D2M8K2.t15618 = [0, 165454457421, 438589034926, 279481873154, 29885616255, 0, 0, 0] := by
  decide +kernel

theorem rows15619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15619 = true := by
  decide +kernel

theorem tot15619 : totK PD2M8K2 D2M8K2.t15619 = [0, 91442232089, 395463863116, 344348466666, 52131638278, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
