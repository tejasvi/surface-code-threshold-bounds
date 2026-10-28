import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9336 = true := by
  decide +kernel

theorem tot9336 : totK PD2M8K2 D2M8K2.t9336 = [0, 177086745037, 456996352407, 237920759217, 17104814242, 0, 0, 0] := by
  decide +kernel

theorem rows9337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9337 = true := by
  decide +kernel

theorem tot9337 : totK PD2M8K2 D2M8K2.t9337 = [0, 0, 299958023252, 496115017472, 89510258080, 1096505104, 0, 0] := by
  decide +kernel

theorem rows9338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9338 = true := by
  decide +kernel

theorem tot9338 : totK PD2M8K2 D2M8K2.t9338 = [0, 86927426491, 299145094058, 386850045965, 110153910190, 3884009855, 0, 0] := by
  decide +kernel

theorem rows9339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9339 = true := by
  decide +kernel

theorem tot9339 : totK PD2M8K2 D2M8K2.t9339 = [0, 151080827423, 485680274851, 246161890392, 9515432130, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
