import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6992 = true := by
  decide +kernel

theorem tot6992 : totK PD2M8K2 D2M8K2.t6992 = [0, 180880358302, 464216423902, 252546816754, 22649316565, 0, 0, 0] := by
  decide +kernel

theorem rows6993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6993 = true := by
  decide +kernel

theorem tot6993 : totK PD2M8K2 D2M8K2.t6993 = [0, 161056428301, 463754430202, 265472588918, 16127117261, 0, 0, 0] := by
  decide +kernel

theorem rows6994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6994 = true := by
  decide +kernel

theorem tot6994 : totK PD2M8K2 D2M8K2.t6994 = [0, 0, 271143088407, 504630112115, 116855339043, 1198073392, 0, 0] := by
  decide +kernel

theorem rows6995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6995 = true := by
  decide +kernel

theorem tot6995 : totK PD2M8K2 D2M8K2.t6995 = [0, 34739637443, 216116352484, 431481700196, 188295040393, 11991925116, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
