import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows444 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t444 = true := by
  decide +kernel

theorem tot444 : totK PA10K2 A10K2.t444 = [0, 0, 429594208047, 1684325013032, 2022722298297, 695657765164, 53844901745, 0, 0, 0] := by
  decide +kernel

theorem rows445 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t445 = true := by
  decide +kernel

theorem tot445 : totK PA10K2 A10K2.t445 = [0, 0, 418918019949, 1743918595128, 1973726434279, 558474606914, 34193440607, 0, 0, 0] := by
  decide +kernel

theorem rows446 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t446 = true := by
  decide +kernel

theorem tot446 : totK PA10K2 A10K2.t446 = [0, 0, 0, 449579964357, 1778442111107, 1772863390360, 449923207410, 25239774317, 0, 0] := by
  decide +kernel

theorem rows447 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t447 = true := by
  decide +kernel

theorem tot447 : totK PA10K2 A10K2.t447 = [0, 0, 451670623937, 1664198343308, 1868504020856, 673860505865, 91585749185, 5365973533, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
