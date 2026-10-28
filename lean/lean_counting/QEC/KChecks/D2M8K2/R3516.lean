import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14064 = true := by
  decide +kernel

theorem tot14064 : totK PD2M8K2 D2M8K2.t14064 = [0, 179700513375, 460223695593, 255696397614, 23041996261, 0, 0, 0] := by
  decide +kernel

theorem rows14065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14065 = true := by
  decide +kernel

theorem tot14065 : totK PD2M8K2 D2M8K2.t14065 = [0, 155365546180, 448337153254, 267006917310, 21547165211, 0, 0, 0] := by
  decide +kernel

theorem rows14066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14066 = true := by
  decide +kernel

theorem tot14066 : totK PD2M8K2 D2M8K2.t14066 = [0, 0, 236860258309, 492034876963, 152410017518, 5710253261, 0, 0] := by
  decide +kernel

theorem rows14067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14067 = true := by
  decide +kernel

theorem tot14067 : totK PD2M8K2 D2M8K2.t14067 = [0, 67163829148, 278001398445, 390137942056, 129106397798, 5883432551, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
