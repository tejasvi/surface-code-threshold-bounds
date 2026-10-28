import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4240 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4240 = true := by
  decide +kernel

theorem tot4240 : totK PA10K2 A10K2.t4240 = [0, 728029506284, 2105189742775, 1635643066193, 378484505236, 25295400199, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4241 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4241 = true := by
  decide +kernel

theorem tot4241 : totK PA10K2 A10K2.t4241 = [287747644888, 1303192349036, 2012461136773, 1185479705375, 197008359770, 5453753178, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4242 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4242 = true := by
  decide +kernel

theorem tot4242 : totK PA10K2 A10K2.t4242 = [307485040078, 1459029445289, 2201134996101, 1032321495562, 98465913777, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4243 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4243 = true := by
  decide +kernel

theorem tot4243 : totK PA10K2 A10K2.t4243 = [282207666598, 1085671291740, 1826185817565, 1448867456392, 367664583433, 25580784005, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
