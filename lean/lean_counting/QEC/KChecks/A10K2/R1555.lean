import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6220 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6220 = true := by
  decide +kernel

theorem tot6220 : totK PA10K2 A10K2.t6220 = [0, 0, 282819497165, 1551911188541, 2171725715550, 699146213513, 53071243415, 0, 0, 0] := by
  decide +kernel

theorem rows6221 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6221 = true := by
  decide +kernel

theorem tot6221 : totK PA10K2 A10K2.t6221 = [0, 0, 271305974298, 1180647985395, 1915286080701, 1101215637212, 189682871468, 6034215561, 0, 0] := by
  decide +kernel

theorem rows6222 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6222 = true := by
  decide +kernel

theorem tot6222 : totK PA10K2 A10K2.t6222 = [0, 0, 546985495730, 1786342352193, 1771036702856, 521927286696, 36819311980, 0, 0, 0] := by
  decide +kernel

theorem rows6223 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6223 = true := by
  decide +kernel

theorem tot6223 : totK PA10K2 A10K2.t6223 = [0, 0, 0, 1051237522210, 2441855471987, 1060414553166, 85512685414, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
