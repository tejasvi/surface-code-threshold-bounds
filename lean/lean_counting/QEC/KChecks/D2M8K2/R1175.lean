import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4700 = true := by
  decide +kernel

theorem tot4700 : totK PD2M8K2 D2M8K2.t4700 = [0, 0, 0, 178475686939, 448763276611, 249026737946, 25191558099, 0] := by
  decide +kernel

theorem rows4701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4701 = true := by
  decide +kernel

theorem tot4701 : totK PD2M8K2 D2M8K2.t4701 = [0, 0, 0, 214155540321, 491368418024, 183115756116, 5206224793, 0] := by
  decide +kernel

theorem rows4702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4702 = true := by
  decide +kernel

theorem tot4702 : totK PD2M8K2 D2M8K2.t4702 = [0, 0, 149931648890, 340871163347, 314853283229, 113860795237, 6524090962, 0] := by
  decide +kernel

theorem rows4703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4703 = true := by
  decide +kernel

theorem tot4703 : totK PD2M8K2 D2M8K2.t4703 = [0, 0, 195884848727, 485245333471, 219629332381, 9407265020, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
