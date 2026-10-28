import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2336 = true := by
  decide +kernel

theorem tot2336 : totK PD2M8K2 D2M8K2.t2336 = [0, 189447561880, 488473202927, 226586035644, 11041838868, 0, 0, 0] := by
  decide +kernel

theorem rows2337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2337 = true := by
  decide +kernel

theorem tot2337 : totK PD2M8K2 D2M8K2.t2337 = [0, 0, 203874023111, 460313229159, 217751690938, 19862268668, 0, 0] := by
  decide +kernel

theorem rows2338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2338 = true := by
  decide +kernel

theorem tot2338 : totK PD2M8K2 D2M8K2.t2338 = [0, 0, 207733796404, 474506322288, 208766522406, 6917919723, 0, 0] := by
  decide +kernel

theorem rows2339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2339 = true := by
  decide +kernel

theorem tot2339 : totK PD2M8K2 D2M8K2.t2339 = [0, 173426155916, 388484681487, 232124425775, 102174663297, 6800370819, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
