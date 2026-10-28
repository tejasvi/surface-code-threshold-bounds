import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6364 = true := by
  decide +kernel

theorem tot6364 : totK PD2M8K2 D2M8K2.t6364 = [0, 83602758792, 325259160964, 369625940960, 95240822639, 3462014130, 0, 0] := by
  decide +kernel

theorem rows6365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6365 = true := by
  decide +kernel

theorem tot6365 : totK PD2M8K2 D2M8K2.t6365 = [0, 176770812176, 450981112953, 267438928735, 27390548975, 0, 0, 0] := by
  decide +kernel

theorem rows6366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6366 = true := by
  decide +kernel

theorem tot6366 : totK PD2M8K2 D2M8K2.t6366 = [0, 157526790404, 456436577475, 255460979875, 14722773229, 0, 0, 0] := by
  decide +kernel

theorem rows6367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6367 = true := by
  decide +kernel

theorem tot6367 : totK PD2M8K2 D2M8K2.t6367 = [0, 0, 286596129105, 513721753425, 89262042315, 1062926506, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
