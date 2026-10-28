import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows660 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t660 = true := by
  decide +kernel

theorem tot660 : totK PA10K2 A10K2.t660 = [0, 123772623487, 938856551155, 1939961896998, 1391004043504, 345164959983, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows661 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t661 = true := by
  decide +kernel

theorem tot661 : totK PA10K2 A10K2.t661 = [0, 212862030042, 1022989097330, 1913338808224, 1403479817175, 230957814468, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows662 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t662 = true := by
  decide +kernel

theorem tot662 : totK PA10K2 A10K2.t662 = [0, 456789380306, 1676938936102, 1912773183273, 647131333808, 52230035883, 0, 0, 0, 0] := by
  decide +kernel

theorem rows663 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t663 = true := by
  decide +kernel

theorem tot663 : totK PA10K2 A10K2.t663 = [0, 110196786130, 1213077798623, 2314852284218, 1036869325686, 81378533866, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
