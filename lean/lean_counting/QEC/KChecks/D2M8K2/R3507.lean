import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14028 = true := by
  decide +kernel

theorem tot14028 : totK PD2M8K2 D2M8K2.t14028 = [0, 0, 280100453249, 510508591999, 96003101698, 1310517177, 0, 0] := by
  decide +kernel

theorem rows14029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14029 = true := by
  decide +kernel

theorem tot14029 : totK PD2M8K2 D2M8K2.t14029 = [0, 166263604103, 434729730036, 292545649937, 36500374125, 0, 0, 0] := by
  decide +kernel

theorem rows14030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14030 = true := by
  decide +kernel

theorem tot14030 : totK PD2M8K2 D2M8K2.t14030 = [0, 174538157248, 475049590862, 235444640305, 12399799556, 0, 0, 0] := by
  decide +kernel

theorem rows14031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14031 = true := by
  decide +kernel

theorem tot14031 : totK PD2M8K2 D2M8K2.t14031 = [0, 88193270072, 320418526803, 360387954913, 132845626161, 15860286962, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
