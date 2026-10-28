import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6416 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6416 = true := by
  decide +kernel

theorem tot6416 : totK PA10K2 A10K2.t6416 = [0, 0, 532211063983, 1885077143703, 1743182873778, 425058032703, 25565504801, 0, 0, 0] := by
  decide +kernel

theorem rows6417 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6417 = true := by
  decide +kernel

theorem tot6417 : totK PA10K2 A10K2.t6417 = [0, 320620677522, 1386261597903, 1925280784675, 998859169616, 166059891026, 5517381808, 0, 0, 0] := by
  decide +kernel

theorem rows6418 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6418 = true := by
  decide +kernel

theorem tot6418 : totK PA10K2 A10K2.t6418 = [0, 201347380062, 1315698520320, 2165244521165, 872868988800, 65953746422, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6419 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6419 = true := by
  decide +kernel

theorem tot6419 : totK PA10K2 A10K2.t6419 = [0, 501702578590, 1663327715875, 1808572830725, 850246183208, 158422455186, 6121173289, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
