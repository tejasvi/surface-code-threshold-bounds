import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6056 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6056 = true := by
  decide +kernel

theorem tot6056 : totK PA10K2 A10K2.t6056 = [482935380090, 1801519363927, 2047727274675, 635339863190, 43332227245, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6057 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6057 = true := by
  decide +kernel

theorem tot6057 : totK PA10K2 A10K2.t6057 = [290890085913, 1444252478044, 2202004649665, 1021929446073, 88563186712, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6058 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6058 = true := by
  decide +kernel

theorem tot6058 : totK PA10K2 A10K2.t6058 = [0, 598382671978, 2010415330646, 1942793495278, 459712223609, 13816090359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6059 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6059 = true := by
  decide +kernel

theorem tot6059 : totK PA10K2 A10K2.t6059 = [0, 300561657718, 1510890316562, 2160728537646, 844825283374, 74643347679, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
